//! `Nat.dist`: the distance function on ℕ, opening `Mathlib.Data.Nat.Dist`
//! (pinned commit `c5ea0035…`, 18 rows) for the autogenesis screen —
//! `docs/plan/status/348-nat-dist-nth.md`.
//!
//! Mathlib: `def dist (n m : ℕ) := n - m + (m - n)`. This is the SAME
//! definition over our own `Nat.sub`/`Nat.add` — not merely a construction
//! that agrees with it pointwise (contrast `Nat.minFac`, `min_fac.rs`, whose
//! module doc explains why THAT mirror must stay open) — so a later `ml430`
//! mirror flip for any `Nat.dist_*` fact is honest under the mirror-flip
//! criterion in `CLAUDE.md`.
//!
//! `Nat.sub` truncates (`3 - 5 = 0`), which is exactly what makes `dist` a
//! genuine two-sided distance rather than a signed difference: at most one of
//! `n - m`/`m - n` is ever nonzero, and the definition adds both so the
//! nonzero one survives regardless of which argument is larger.
//! `dist_evaluates_correctly` (`nat_prelude_tests.rs`) checks concrete values
//! on both sides of that asymmetry, including the truncating direction.
//!
//! Seven theorems are declared alongside the definition, each a genuine
//! Mathlib statement (comm/self/the two `sub`-orientation lemmas/the two zero
//! boundaries/`succ_succ`), not the full 18-row surface — the remaining rows
//! are ordinary proof work for whichever future lane draws them as facts.

use super::NatPrelude;
use super::ops::{NatDev, NatOps};
use crate::KernelError;
use crate::env::Declaration;
use crate::env::ReducibilityHint;

/// `Nat.dist`, `dist_comm`, `dist_self`, `dist_eq_sub_of_le[_right]`,
/// `dist_zero_right`/`dist_zero_left`, `dist_succ_succ`.
pub(super) fn declare_dist_all(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();

    // Nat.dist n m := add (sub n m) (sub m n)
    {
        let n_fv = d.fresh_fvar();
        let m_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let m = d.kernel().fvar(m_fv);
        let sub_nm = d.sub(n, m);
        let sub_mn = d.sub(m, n);
        let body = d.add(sub_nm, sub_mn);
        let value = {
            let inner = d.lam_fv(m_fv, nat, body);
            d.lam_fv(n_fv, nat, inner)
        };
        let ty = {
            let inner = d.arrow(nat, nat);
            d.arrow(nat, inner)
        };
        // Strictly greater delta height than `add` (1) and `sub` (2), the two
        // definitions it calls.
        d.kernel().add_declaration(Declaration::Definition {
            name: p.dist,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(3),
        })?;
    }

    // dist_comm : ∀ n m, Eq (dist n m) (dist m n)
    d.theorem(p.dist_comm, 2, &|d, v| {
        let (n, m) = (v[0], v[1]);
        let dist_nm = d.const_app(p.dist, &[n, m]);
        let dist_mn = d.const_app(p.dist, &[m, n]);
        let stmt = d.eq(dist_nm, dist_mn);
        let sub_nm = d.sub(n, m);
        let sub_mn = d.sub(m, n);
        // dist n m ≡ add(sub n m, sub m n); dist m n ≡ add(sub m n, sub n m);
        // `add_comm` on those two subtractions IS the statement, by defeq.
        let proof = d.lemma(p.add_comm, &[sub_nm, sub_mn]);
        (stmt, proof)
    })?;

    // dist_self : ∀ n, Eq (dist n n) zero
    d.theorem(p.dist_self, 1, &|d, v| {
        let n = v[0];
        let dist_nn = d.const_app(p.dist, &[n, n]);
        let zero = d.zero();
        let stmt = d.eq(dist_nn, zero);
        let sub_nn = d.sub(n, n);
        let h1 = d.lemma(p.sub_self, &[n]); // Eq (sub n n) zero
        // Eq (add(sub_nn,sub_nn)) (add(zero,zero)) ≡ Eq dist_nn (add zero zero)
        let step1 = d.congr(sub_nn, zero, h1, &|d, x| d.add(x, x));
        let add_zero_zero = d.add(zero, zero);
        let h2 = d.lemma(p.zero_add, &[zero]); // Eq (add zero zero) zero
        let proof = d.trans(dist_nn, add_zero_zero, zero, step1, h2);
        (stmt, proof)
    })?;

    // dist_eq_sub_of_le : ∀ n m, Le n m → Eq (dist n m) (sub m n)
    d.theorem(p.dist_eq_sub_of_le, 2, &|d, v| {
        let (n, m) = (v[0], v[1]);
        let hyp_ty = d.le(n, m);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let dist_nm = d.const_app(p.dist, &[n, m]);
        let sub_mn = d.sub(m, n);
        let concl = d.eq(dist_nm, sub_mn);
        let sub_nm = d.sub(n, m);
        let zero = d.zero();
        let h1 = d.lemma(p.sub_eq_zero_of_le, &[n, m, h]); // Eq (sub n m) zero
        let step1 = d.congr(sub_nm, zero, h1, &|d, x| d.add(x, sub_mn));
        let add_zero_submn = d.add(zero, sub_mn);
        let h2 = d.lemma(p.zero_add, &[sub_mn]); // Eq (add zero (sub m n)) (sub m n)
        let body = d.trans(dist_nm, add_zero_submn, sub_mn, step1, h2);
        let stmt = d.arrow(hyp_ty, concl);
        let proof = d.lam_fv(h_fv, hyp_ty, body);
        (stmt, proof)
    })?;

    // dist_eq_sub_of_le_right : ∀ n m, Le m n → Eq (dist n m) (sub n m)
    d.theorem(p.dist_eq_sub_of_le_right, 2, &|d, v| {
        let (n, m) = (v[0], v[1]);
        let hyp_ty = d.le(m, n);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let dist_nm = d.const_app(p.dist, &[n, m]);
        let sub_nm = d.sub(n, m);
        let concl = d.eq(dist_nm, sub_nm);
        let sub_mn = d.sub(m, n);
        let zero = d.zero();
        let h1 = d.lemma(p.sub_eq_zero_of_le, &[m, n, h]); // Eq (sub m n) zero
        let step1 = d.congr(sub_mn, zero, h1, &|d, x| d.add(sub_nm, x));
        let add_subnm_zero = d.add(sub_nm, zero);
        let h2 = d.lemma(p.add_zero, &[sub_nm]); // Eq (add (sub n m) zero) (sub n m)
        let body = d.trans(dist_nm, add_subnm_zero, sub_nm, step1, h2);
        let stmt = d.arrow(hyp_ty, concl);
        let proof = d.lam_fv(h_fv, hyp_ty, body);
        (stmt, proof)
    })?;

    // dist_zero_right : ∀ n, Eq (dist n zero) n
    // — via dist_eq_sub_of_le_right at m := zero, h := zero_le n, then sub_zero.
    d.theorem(p.dist_zero_right, 1, &|d, v| {
        let n = v[0];
        let zero = d.zero();
        let dist_n0 = d.const_app(p.dist, &[n, zero]);
        let stmt = d.eq(dist_n0, n);
        let h_le = d.lemma(p.zero_le, &[n]); // Le zero n
        let h1 = d.lemma(p.dist_eq_sub_of_le_right, &[n, zero, h_le]); // Eq (dist n 0) (sub n 0)
        let sub_n0 = d.sub(n, zero);
        let h2 = d.lemma(p.sub_zero, &[n]); // Eq (sub n 0) n
        let proof = d.trans(dist_n0, sub_n0, n, h1, h2);
        (stmt, proof)
    })?;

    // dist_zero_left : ∀ n, Eq (dist zero n) n
    // — via dist_eq_sub_of_le at n := zero, h := zero_le n, then sub_zero.
    d.theorem(p.dist_zero_left, 1, &|d, v| {
        let n = v[0];
        let zero = d.zero();
        let dist_0n = d.const_app(p.dist, &[zero, n]);
        let stmt = d.eq(dist_0n, n);
        let h_le = d.lemma(p.zero_le, &[n]); // Le zero n
        let h1 = d.lemma(p.dist_eq_sub_of_le, &[zero, n, h_le]); // Eq (dist 0 n) (sub n 0)
        let sub_n0 = d.sub(n, zero);
        let h2 = d.lemma(p.sub_zero, &[n]); // Eq (sub n 0) n
        let proof = d.trans(dist_0n, sub_n0, n, h1, h2);
        (stmt, proof)
    })?;

    // dist_succ_succ : ∀ n m, Eq (dist (succ n) (succ m)) (dist n m)
    d.theorem(p.dist_succ_succ, 2, &|d, v| {
        let (n, m) = (v[0], v[1]);
        let sn = d.succ(n);
        let sm = d.succ(m);
        let dist_ss = d.const_app(p.dist, &[sn, sm]);
        let dist_nm = d.const_app(p.dist, &[n, m]);
        let stmt = d.eq(dist_ss, dist_nm);

        let sub_sn_sm = d.sub(sn, sm);
        let sub_n_m = d.sub(n, m);
        let sub_sm_sn = d.sub(sm, sn);
        let sub_m_n = d.sub(m, n);

        let h1 = d.lemma(p.succ_sub_succ, &[n, m]); // Eq (sub (succ n)(succ m)) (sub n m)
        let h2 = d.lemma(p.succ_sub_succ, &[m, n]); // Eq (sub (succ m)(succ n)) (sub m n)

        // add(sub_sn_sm, sub_sm_sn) --[h1]--> add(sub_n_m, sub_sm_sn)
        //                            --[h2]--> add(sub_n_m, sub_m_n)
        let step_a = d.congr(sub_sn_sm, sub_n_m, h1, &|d, x| d.add(x, sub_sm_sn));
        let mid = d.add(sub_n_m, sub_sm_sn);
        let step_b = d.congr(sub_sm_sn, sub_m_n, h2, &|d, x| d.add(sub_n_m, x));
        let proof = d.trans(dist_ss, mid, dist_nm, step_a, step_b);
        (stmt, proof)
    })?;

    Ok(())
}
