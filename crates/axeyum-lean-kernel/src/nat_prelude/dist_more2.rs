//! Three more `Nat.dist` `ml430` mirrors, on top of `dist.rs`'s seven and
//! `dist.rs`'s draw-9 `declare_dist_more_all` six: `Nat.dist_pos_of_ne`,
//! `Nat.dist_eq_intro`, and `Nat.dist_triangle_inequality`.
//! `docs/plan/status/draw9-second-theorems.md`.
//!
//! # `dist_pos_of_ne`
//!
//! `i ≠ j` splits (via `fermat_number_mirrors.rs`'s `lt_or_gt_of_ne_local`)
//! into `Lt i j` / `Lt j i`; each branch rewrites `dist` to a `sub` via
//! `dist_eq_sub_of_le[_right]` and shows that `sub` positive from the strict
//! order (`sub_pos_of_lt`, built here from `sub_add_cancel` plus
//! `fermat_number_mirrors.rs`'s `pos_of_lt_add_left`).
//!
//! # `dist_eq_intro`
//!
//! Case-split `Le k n` vs `Le n k` (`le_total`). In the `Le k n` branch,
//! `e := sub n k` witnesses `n = e + k`; substituting into the hypothesis
//! and cancelling `k` on the left gives `m = e + l`, hence (after a `dist`
//! rewrite on each side) `dist n k = e = dist l m`. The other branch is the
//! SAME argument with `(n, k)` and `(k, n)` swapped, converted back via
//! `dist_comm` twice (`dist_eq_intro_half`, called with the roles
//! exchanged).
//!
//! # `dist_triangle_inequality`
//!
//! `sub_le_dist_sum(a, b, c)` proves `sub a c ≤ dist a b + dist b c`, via
//! `a ≤ b + sub a b` (`le_add_sub_self`, general and unconditional),
//! `sub a b ≤ dist a b` (`le_add_right`), the same pair for `b`/`c`, and
//! `sub_le_iff_le_add` to fold the resulting `≤` back through `sub`. Two
//! instances (`(n, m, k)` and `(k, m, n)`, the second rewritten through
//! `dist_comm` twice) bound BOTH `sub n k` and `sub k n` by `dist n m + dist
//! m k`; since `dist n k` is their SUM and at most one is nonzero
//! (`le_total n k`), either bound alone closes the goal.

use super::NatPrelude;
use super::fermat_number_mirrors::{lt_or_gt_of_ne_local, pos_of_lt_add_left};
use super::finite::le_of_lt;
use super::ops::{NatDev, NatOps};
use super::primes::or_cases;
use crate::KernelError;
use crate::expr::ExprId;

/// `sub_pos_of_lt : Lt a b ⊢ Lt zero (sub b a)`. From `Lt a b`, `sub_add_
/// cancel` gives `b = add (sub b a) a`, so (rewriting via `add_comm`)
/// `b = add a (sub b a)`; transporting `hlt` along that equation gives
/// `Lt a (add a (sub b a))`, and `pos_of_lt_add_left` finishes.
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

/// `Nat.dist_pos_of_ne : ∀ i j, Not (Eq i j) → Lt zero (dist i j)`.
fn declare_dist_pos_of_ne(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.dist_pos_of_ne, 2, &|d, v| {
        let (i, j) = (v[0], v[1]);
        let eq_ij = d.eq(i, j);
        let hne_ty = d.const_app(p.logic.not, &[eq_ij]);
        let hne_fv = d.fresh_fvar();
        let hne = d.kernel().fvar(hne_fv);

        let dist_ij = d.const_app(p.dist, &[i, j]);
        let zero = d.zero();
        let concl = d.lt(zero, dist_ij);

        let split = lt_or_gt_of_ne_local(d, &p, i, j, hne); // Or (Lt i j) (Lt j i)
        let lt_ij_ty = d.lt(i, j);
        let lt_ji_ty = d.lt(j, i);

        let on_lt_ij = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let h_le = le_of_lt(d, &p, i, j, h);
            let dist_eq = d.lemma(p.dist_eq_sub_of_le, &[i, j, h_le]); // Eq dist_ij (sub j i)
            let sub_ji = d.sub(j, i);
            let pos_sub = sub_pos_of_lt(d, &p, i, j, h); // Lt zero (sub j i)
            let motive = d.eq_motive(sub_ji, &|d, x| d.lt(zero, x));
            let dist_eq_rev = d.symm(dist_ij, sub_ji, dist_eq); // Eq sub_ji dist_ij
            let body = d.transport(sub_ji, motive, pos_sub, dist_ij, dist_eq_rev);
            d.lam_fv(h_fv, lt_ij_ty, body)
        };
        let on_lt_ji = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let h_le = le_of_lt(d, &p, j, i, h);
            let dist_eq = d.lemma(p.dist_eq_sub_of_le_right, &[i, j, h_le]); // Eq dist_ij (sub i j)
            let sub_ij = d.sub(i, j);
            let pos_sub = sub_pos_of_lt(d, &p, j, i, h); // Lt zero (sub i j)
            let motive = d.eq_motive(sub_ij, &|d, x| d.lt(zero, x));
            let dist_eq_rev = d.symm(dist_ij, sub_ij, dist_eq);
            let body = d.transport(sub_ij, motive, pos_sub, dist_ij, dist_eq_rev);
            d.lam_fv(h_fv, lt_ji_ty, body)
        };

        let case_result = or_cases(d, &p, lt_ij_ty, lt_ji_ty, concl, on_lt_ij, on_lt_ji, split);
        let stmt = d.arrow(hne_ty, concl);
        let proof = d.lam_fv(hne_fv, hne_ty, case_result);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Le k n`, `hyp : Eq (add n m) (add k l) ⊢ Eq (dist n k) (dist l m)`.
/// See the module doc's `dist_eq_intro` section.
#[allow(clippy::too_many_arguments)]
fn dist_eq_intro_half(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    n: ExprId,
    m: ExprId,
    k: ExprId,
    l: ExprId,
    h_le_kn: ExprId,
    hyp: ExprId,
) -> ExprId {
    let p = *p;
    let e = d.sub(n, k);
    let add_e_k = d.add(e, k);
    let h_cancel = d.lemma(p.sub_add_cancel, &[k, n, h_le_kn]); // Eq add_e_k n
    let n_eq_addek = d.symm(add_e_k, n, h_cancel); // Eq n add_e_k

    let add_n_m = d.add(n, m);
    let add_k_l = d.add(k, l);
    let add_addek_m = d.add(add_e_k, m);
    let cong1 = d.congr(n, add_e_k, n_eq_addek, &|d, x| d.add(x, m)); // Eq add_n_m add_addek_m
    let cong1_rev = d.symm(add_n_m, add_addek_m, cong1);
    let hyp2 = d.trans(add_addek_m, add_n_m, add_k_l, cong1_rev, hyp); // Eq add_addek_m add_k_l

    let add_k_e = d.add(k, e);
    let h_comm_ek = d.lemma(p.add_comm, &[e, k]); // Eq add_e_k add_k_e
    let add_addke_m = d.add(add_k_e, m);
    let cong2 = d.congr(add_e_k, add_k_e, h_comm_ek, &|d, x| d.add(x, m)); // Eq add_addek_m add_addke_m
    let add_e_m = d.add(e, m);
    let add_k_addem = d.add(k, add_e_m);
    let h_assoc = d.lemma(p.add_assoc, &[k, e, m]); // Eq add_addke_m add_k_addem
    let lhs_to_mid = d.trans(add_addek_m, add_addke_m, add_k_addem, cong2, h_assoc); // Eq add_addek_m add_k_addem
    let lhs_to_mid_rev = d.symm(add_addek_m, add_k_addem, lhs_to_mid);
    let hyp3 = d.trans(add_k_addem, add_addek_m, add_k_l, lhs_to_mid_rev, hyp2); // Eq add_k_addem add_k_l

    let em_eq_l = d.lemma(p.add_left_cancel, &[k, add_e_m, l, hyp3]); // Eq add_e_m l

    let add_m_e = d.add(m, e);
    let h_comm_em = d.lemma(p.add_comm, &[e, m]); // Eq add_e_m add_m_e
    let h_comm_em_rev = d.symm(add_e_m, add_m_e, h_comm_em);
    let l_eq_via_me = d.trans(add_m_e, add_e_m, l, h_comm_em_rev, em_eq_l); // Eq add_m_e l

    let le_m_addme = d.lemma(p.le_add_right, &[m, e]); // Le m (add m e)
    let motive_le = d.eq_motive(add_m_e, &|d, x| d.le(m, x));
    let h_le_ml = d.transport(add_m_e, motive_le, le_m_addme, l, l_eq_via_me); // Le m l

    let dist_nk = d.const_app(p.dist, &[n, k]);
    let dist_lm = d.const_app(p.dist, &[l, m]);
    let dist_nk_eq_e = d.lemma(p.dist_eq_sub_of_le_right, &[n, k, h_le_kn]); // Eq dist_nk e

    let dist_lm_eq_subl_m = d.lemma(p.dist_eq_sub_of_le_right, &[l, m, h_le_ml]); // Eq dist_lm (sub l m)
    let l_eq_addme_rev = d.symm(add_m_e, l, l_eq_via_me); // Eq l add_m_e
    let sub_l_m = d.sub(l, m);
    let sub_addme_m = d.sub(add_m_e, m);
    let cong_subl = d.congr(l, add_m_e, l_eq_addme_rev, &|d, x| d.sub(x, m)); // Eq sub_l_m sub_addme_m
    let h_cancel_left = d.lemma(p.add_sub_cancel_left, &[m, e]); // Eq sub_addme_m e
    let sub_lm_eq_e = d.trans(sub_l_m, sub_addme_m, e, cong_subl, h_cancel_left); // Eq sub_l_m e
    let dist_lm_eq_e = d.trans(dist_lm, sub_l_m, e, dist_lm_eq_subl_m, sub_lm_eq_e); // Eq dist_lm e

    let dist_lm_eq_e_rev = d.symm(dist_lm, e, dist_lm_eq_e);
    d.trans(dist_nk, e, dist_lm, dist_nk_eq_e, dist_lm_eq_e_rev)
}

/// `Nat.dist_eq_intro : ∀ n m k l, Eq (add n m) (add k l) → Eq (dist n k)
/// (dist l m)`.
fn declare_dist_eq_intro(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.dist_eq_intro, 4, &|d, v| {
        let (n, m, k, l) = (v[0], v[1], v[2], v[3]);
        let add_nm = d.add(n, m);
        let add_kl = d.add(k, l);
        let hyp_ty = d.eq(add_nm, add_kl);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);

        let dist_nk = d.const_app(p.dist, &[n, k]);
        let dist_lm = d.const_app(p.dist, &[l, m]);
        let concl = d.eq(dist_nk, dist_lm);

        let total = d.lemma(p.le_total, &[k, n]); // Or (Le k n) (Le n k)
        let le_kn_ty = d.le(k, n);
        let le_nk_ty = d.le(n, k);

        let on_le_kn = {
            let hh_fv = d.fresh_fvar();
            let hh = d.kernel().fvar(hh_fv);
            let body = dist_eq_intro_half(d, &p, n, m, k, l, hh, h);
            d.lam_fv(hh_fv, le_kn_ty, body)
        };
        let on_le_nk = {
            let hh_fv = d.fresh_fvar();
            let hh = d.kernel().fvar(hh_fv);
            let h_swapped = d.symm(add_nm, add_kl, h); // Eq add_kl add_nm
            let sub_result = dist_eq_intro_half(d, &p, k, l, n, m, hh, h_swapped); // Eq (dist k n)(dist m l)
            let dist_kn = d.const_app(p.dist, &[k, n]);
            let dist_ml = d.const_app(p.dist, &[m, l]);
            let comm1 = d.lemma(p.dist_comm, &[k, n]); // Eq dist_kn dist_nk
            let comm2 = d.lemma(p.dist_comm, &[m, l]); // Eq dist_ml dist_lm
            let step_a = d.symm(dist_kn, dist_nk, comm1); // Eq dist_nk dist_kn
            let (_, body) = d.chain(
                dist_nk,
                &[(dist_kn, step_a), (dist_ml, sub_result), (dist_lm, comm2)],
            );
            d.lam_fv(hh_fv, le_nk_ty, body)
        };

        let case_result = or_cases(d, &p, le_kn_ty, le_nk_ty, concl, on_le_kn, on_le_nk, total);
        let stmt = d.arrow(hyp_ty, concl);
        let proof = d.lam_fv(h_fv, hyp_ty, case_result);
        (stmt, proof)
    })?;
    Ok(())
}

/// `le_add_sub_self : ∀ m n, Le n (add m (sub n m))` — general, no order
/// hypothesis needed. `Le n m` (`le_total`'s first branch): `sub n m = 0`
/// (`sub_eq_zero_of_le`), so `add m (sub n m) = m` (`add_zero`), and the
/// goal is exactly the branch hypothesis. `Le m n`: `sub_add_cancel` gives
/// `add (sub n m) m = n`; commuting gives `add m (sub n m) = n`, so the goal
/// is `Le n n` (`le_refl`).
fn le_add_sub_self(d: &mut NatDev<'_>, p: &NatPrelude, m: ExprId, n: ExprId) -> ExprId {
    let p = *p;
    let sub_nm = d.sub(n, m);
    let add_m_subnm = d.add(m, sub_nm);
    let goal = d.le(n, add_m_subnm);

    let total = d.lemma(p.le_total, &[n, m]); // Or (Le n m) (Le m n)
    let le_nm_ty = d.le(n, m);
    let le_mn_ty = d.le(m, n);

    let on_le_nm = {
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let zero = d.zero();
        let sub_eq_zero = d.lemma(p.sub_eq_zero_of_le, &[n, m, h]); // Eq sub_nm zero
        let add_m_zero = d.add(m, zero);
        let cong = d.congr(sub_nm, zero, sub_eq_zero, &|d, x| d.add(m, x)); // Eq add_m_subnm add_m_zero
        let m_eq = d.lemma(p.add_zero, &[m]); // Eq add_m_zero m
        let addmsubnm_eq_m = d.trans(add_m_subnm, add_m_zero, m, cong, m_eq); // Eq add_m_subnm m
        let m_eq_rev = d.symm(add_m_subnm, m, addmsubnm_eq_m); // Eq m add_m_subnm
        let motive = d.eq_motive(m, &|d, x| d.le(n, x));
        let body = d.transport(m, motive, h, add_m_subnm, m_eq_rev);
        d.lam_fv(h_fv, le_nm_ty, body)
    };
    let on_le_mn = {
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let add_subnm_m = d.add(sub_nm, m);
        let h_cancel = d.lemma(p.sub_add_cancel, &[m, n, h]); // Eq add_subnm_m n
        let h_comm = d.lemma(p.add_comm, &[m, sub_nm]); // Eq add_m_subnm add_subnm_m
        let addm_eq_n = d.trans(add_m_subnm, add_subnm_m, n, h_comm, h_cancel); // Eq add_m_subnm n
        let n_eq_addm = d.symm(add_m_subnm, n, addm_eq_n); // Eq n add_m_subnm
        let le_refl_n = d.lemma(p.le_refl, &[n]);
        let motive = d.eq_motive(n, &|d, x| d.le(n, x));
        let body = d.transport(n, motive, le_refl_n, add_m_subnm, n_eq_addm);
        d.lam_fv(h_fv, le_mn_ty, body)
    };

    or_cases(d, &p, le_nm_ty, le_mn_ty, goal, on_le_nm, on_le_mn, total)
}

/// `sub_le_dist_sum : ∀ a b c, Le (sub a c) (add (dist a b) (dist b c))`.
/// See the module doc's `dist_triangle_inequality` section.
fn sub_le_dist_sum(d: &mut NatDev<'_>, p: &NatPrelude, a: ExprId, b: ExprId, c: ExprId) -> ExprId {
    let p = *p;
    let d1 = d.const_app(p.dist, &[a, b]);
    let d2 = d.const_app(p.dist, &[b, c]);
    let s = d.add(d1, d2);

    let sub_ab = d.sub(a, b);
    let sub_ba = d.sub(b, a);
    let le_subab_d1 = d.lemma(p.le_add_right, &[sub_ab, sub_ba]); // Le sub_ab d1
    let a_le_addb_subab = le_add_sub_self(d, &p, b, a); // Le a (add b sub_ab)
    let mono1 = d.lemma(p.add_le_add_left, &[b, sub_ab, d1, le_subab_d1]); // Le (add b sub_ab)(add b d1)
    let add_b_subab = d.add(b, sub_ab);
    let add_b_d1 = d.add(b, d1);
    let a_le_addb_d1 = d.lemma(
        p.le_trans,
        &[a, add_b_subab, add_b_d1, a_le_addb_subab, mono1],
    );

    let sub_bc = d.sub(b, c);
    let sub_cb = d.sub(c, b);
    let le_subbc_d2 = d.lemma(p.le_add_right, &[sub_bc, sub_cb]); // Le sub_bc d2
    let b_le_addc_subbc = le_add_sub_self(d, &p, c, b); // Le b (add c sub_bc)
    let mono2 = d.lemma(p.add_le_add_left, &[c, sub_bc, d2, le_subbc_d2]);
    let add_c_subbc = d.add(c, sub_bc);
    let add_c_d2 = d.add(c, d2);
    let b_le_addc_d2 = d.lemma(
        p.le_trans,
        &[b, add_c_subbc, add_c_d2, b_le_addc_subbc, mono2],
    );

    let mono3 = d.lemma(p.add_le_add_right, &[d1, b, add_c_d2, b_le_addc_d2]); // Le add_b_d1 add_addcd2_d1
    let add_addcd2_d1 = d.add(add_c_d2, d1);
    let a_le_addcd2_d1 = d.lemma(
        p.le_trans,
        &[a, add_b_d1, add_addcd2_d1, a_le_addb_d1, mono3],
    );

    let h_assoc = d.lemma(p.add_assoc, &[c, d2, d1]); // Eq add_addcd2_d1 (add c (add d2 d1))
    let add_d2_d1 = d.add(d2, d1);
    let mid1 = d.add(c, add_d2_d1);
    let h_comm_d = d.lemma(p.add_comm, &[d2, d1]); // Eq add_d2_d1 s
    let cong_inner = d.congr(add_d2_d1, s, h_comm_d, &|d, x| d.add(c, x)); // Eq mid1 (add c s)
    let add_c_s = d.add(c, s);
    let eq_final = d.trans(add_addcd2_d1, mid1, add_c_s, h_assoc, cong_inner); // Eq add_addcd2_d1 add_c_s

    let motive = d.eq_motive(add_addcd2_d1, &|d, x| d.le(a, x));
    let a_le_c_s = d.transport(add_addcd2_d1, motive, a_le_addcd2_d1, add_c_s, eq_final); // Le a add_c_s

    let add_s_c = d.add(s, c);
    let h_comm_cs = d.lemma(p.add_comm, &[c, s]); // Eq add_c_s add_s_c
    let motive2 = d.eq_motive(add_c_s, &|d, x| d.le(a, x));
    let a_le_s_c = d.transport(add_c_s, motive2, a_le_c_s, add_s_c, h_comm_cs); // Le a add_s_c

    let iff_lemma = d.lemma(p.sub_le_iff_le_add, &[a, c, s]); // Iff (Le (sub a c) s) (Le a (add s c))
    let sub_ac = d.sub(a, c);
    let sub_ac_ty = d.le(sub_ac, s);
    let a_le_sc_ty = d.le(a, add_s_c);
    let mpr = d.const_app(p.logic.iff_mpr, &[sub_ac_ty, a_le_sc_ty, iff_lemma]);
    d.apply(mpr, &[a_le_s_c])
}
/// `Nat.dist_triangle_inequality : ∀ n m k, Le (dist n k) (add (dist n m)
/// (dist m k))`.
fn declare_dist_triangle_inequality(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.dist_triangle_inequality, 3, &|d, v| {
        let (n, m, k) = (v[0], v[1], v[2]);
        let d1 = d.const_app(p.dist, &[n, m]);
        let d2 = d.const_app(p.dist, &[m, k]);
        let s = d.add(d1, d2);
        let dist_nk = d.const_app(p.dist, &[n, k]);
        let concl = d.le(dist_nk, s);

        let sub_nk_le_s = sub_le_dist_sum(d, &p, n, m, k); // Le (sub n k) s

        let raw = sub_le_dist_sum(d, &p, k, m, n); // Le (sub k n)(add (dist k m)(dist m n))
        let dist_km = d.const_app(p.dist, &[k, m]);
        let dist_mn = d.const_app(p.dist, &[m, n]);
        let dist_mk = d.const_app(p.dist, &[m, k]);
        let dist_nm = d.const_app(p.dist, &[n, m]);
        let comm_km = d.lemma(p.dist_comm, &[k, m]); // Eq dist_km dist_mk
        let comm_mn = d.lemma(p.dist_comm, &[m, n]); // Eq dist_mn dist_nm
        let raw_rhs = d.add(dist_km, dist_mn);
        let mid_a = d.add(dist_mk, dist_mn);
        let cong_a = d.congr(dist_km, dist_mk, comm_km, &|d, x| d.add(x, dist_mn));
        let mid_b = d.add(dist_mk, dist_nm);
        let cong_b = d.congr(dist_mn, dist_nm, comm_mn, &|d, x| d.add(dist_mk, x));
        let comm_final = d.lemma(p.add_comm, &[dist_mk, dist_nm]); // Eq mid_b s
        let (_, raw_to_s) = d.chain(
            raw_rhs,
            &[(mid_a, cong_a), (mid_b, cong_b), (s, comm_final)],
        );
        let sub_kn = d.sub(k, n);
        let motive3 = d.eq_motive(raw_rhs, &|d, x| d.le(sub_kn, x));
        let sub_kn_le_s = d.transport(raw_rhs, motive3, raw, s, raw_to_s); // Le (sub k n) s

        let total = d.lemma(p.le_total, &[n, k]); // Or (Le n k) (Le k n)
        let le_nk_ty = d.le(n, k);
        let le_kn_ty = d.le(k, n);

        let on_le_nk = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let dist_eq = d.lemma(p.dist_eq_sub_of_le, &[n, k, h]); // Eq dist_nk sub_kn
            let motive = d.eq_motive(sub_kn, &|d, x| d.le(x, s));
            let dist_eq_rev = d.symm(dist_nk, sub_kn, dist_eq); // Eq sub_kn dist_nk
            let body = d.transport(sub_kn, motive, sub_kn_le_s, dist_nk, dist_eq_rev);
            d.lam_fv(h_fv, le_nk_ty, body)
        };
        let on_le_kn = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let sub_nk = d.sub(n, k);
            let dist_eq = d.lemma(p.dist_eq_sub_of_le_right, &[n, k, h]); // Eq dist_nk sub_nk
            let motive = d.eq_motive(sub_nk, &|d, x| d.le(x, s));
            let dist_eq_rev = d.symm(dist_nk, sub_nk, dist_eq); // Eq sub_nk dist_nk
            let body = d.transport(sub_nk, motive, sub_nk_le_s, dist_nk, dist_eq_rev);
            d.lam_fv(h_fv, le_kn_ty, body)
        };

        let proof = or_cases(d, &p, le_nk_ty, le_kn_ty, concl, on_le_nk, on_le_kn, total);
        (concl, proof)
    })?;
    Ok(())
}

/// Declare [`declare_dist_pos_of_ne`], [`declare_dist_eq_intro`], and
/// [`declare_dist_triangle_inequality`].
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_dist_more2_all(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    declare_dist_pos_of_ne(d, p)?;
    declare_dist_eq_intro(d, p)?;
    declare_dist_triangle_inequality(d, p)?;
    Ok(())
}
