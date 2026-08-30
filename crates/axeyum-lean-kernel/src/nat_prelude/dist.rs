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
use crate::expr::ExprId;

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

/// `Nat.dist_eq_zero : ∀ n m, Eq n m → Eq (dist n m) zero` — `Eq.rec`
/// transport of `dist_self` along the hypothesis: the motive
/// `fun x => Eq (dist n x) zero` holds at `x := n` by `dist_self`, and
/// transports along `h : Eq n m` to hold at `x := m`.
fn declare_dist_eq_zero(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.dist_eq_zero, 2, &|d, v| {
        let (n, m) = (v[0], v[1]);
        let hyp_ty = d.eq(n, m);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let dist_nm = d.const_app(p.dist, &[n, m]);
        let zero = d.zero();
        let concl = d.eq(dist_nm, zero);
        let motive = d.eq_motive(n, &|d, x| {
            let dist_nx = d.const_app(p.dist, &[n, x]);
            d.eq(dist_nx, zero)
        });
        let refl_case = d.lemma(p.dist_self, &[n]); // Eq (dist n n) zero
        let body = d.transport(n, motive, refl_case, m, h);
        let stmt = d.arrow(hyp_ty, concl);
        let proof = d.lam_fv(h_fv, hyp_ty, body);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Nat.add_sub_add_left : ∀ k n m, Eq (sub (add k n) (add k m)) (sub n m)` —
/// by induction on `k`. Base (`k = 0`): both sides rewrite to `sub n m` via
/// `zero_add`. Step (`k = succ j`, `ih : ∀ a b, Eq (sub (add j a) (add j b))
/// (sub a b)`): `succ_add` congruence moves `succ` outward on both operands,
/// `succ_sub_succ` strips it, then `ih` at `(n, m)` finishes. Pure arithmetic
/// helper for `dist_add_add_left`; not itself an `ml430` mirror.
fn declare_add_sub_add_left(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.add_sub_add_left, 3, &|d, v| {
        let (k, n, m) = (v[0], v[1], v[2]);

        let statement = |d: &mut NatDev<'_>, kk: ExprId| -> ExprId {
            let a_fv = d.fresh_fvar();
            let a = d.kernel().fvar(a_fv);
            let b_fv = d.fresh_fvar();
            let b = d.kernel().fvar(b_fv);
            let add_ka = d.add(kk, a);
            let add_kb = d.add(kk, b);
            let sub_lhs = d.sub(add_ka, add_kb);
            let sub_rhs = d.sub(a, b);
            let body = d.eq(sub_lhs, sub_rhs);
            let nat2 = d.nat_ty();
            let inner = d.pi_fv(b_fv, nat2, body);
            d.pi_fv(a_fv, nat2, inner)
        };

        let base = |d: &mut NatDev<'_>| -> ExprId {
            let a_fv = d.fresh_fvar();
            let a = d.kernel().fvar(a_fv);
            let b_fv = d.fresh_fvar();
            let b = d.kernel().fvar(b_fv);
            let zero = d.zero();
            let add_0a = d.add(zero, a);
            let add_0b = d.add(zero, b);
            let sub_lhs = d.sub(add_0a, add_0b);
            let sub_rhs = d.sub(a, b);

            let h1 = d.lemma(p.zero_add, &[a]); // Eq (add 0 a) a
            let h2 = d.lemma(p.zero_add, &[b]); // Eq (add 0 b) b
            let step_a = d.congr(add_0a, a, h1, &|d, x| d.sub(x, add_0b));
            let mid = d.sub(a, add_0b);
            let step_b = d.congr(add_0b, b, h2, &|d, x| d.sub(a, x));
            let proof_body = d.trans(sub_lhs, mid, sub_rhs, step_a, step_b);
            let nat2 = d.nat_ty();
            let inner = d.lam_fv(b_fv, nat2, proof_body);
            d.lam_fv(a_fv, nat2, inner)
        };

        let step = |d: &mut NatDev<'_>, j: ExprId, ih: ExprId| -> ExprId {
            let a_fv = d.fresh_fvar();
            let a = d.kernel().fvar(a_fv);
            let b_fv = d.fresh_fvar();
            let b = d.kernel().fvar(b_fv);
            let sj = d.succ(j);
            let add_sja = d.add(sj, a);
            let add_sjb = d.add(sj, b);
            let sub_lhs = d.sub(add_sja, add_sjb);
            let sub_rhs = d.sub(a, b);

            let add_ja = d.add(j, a);
            let add_jb = d.add(j, b);
            let succ_add_ja = d.succ(add_ja);
            let succ_add_jb = d.succ(add_jb);

            let h1 = d.lemma(p.succ_add, &[j, a]); // Eq (add (succ j) a) (succ (add j a))
            let h2 = d.lemma(p.succ_add, &[j, b]); // Eq (add (succ j) b) (succ (add j b))

            let step_a = d.congr(add_sja, succ_add_ja, h1, &|d, x| d.sub(x, add_sjb));
            let mid1 = d.sub(succ_add_ja, add_sjb);
            let step_b = d.congr(add_sjb, succ_add_jb, h2, &|d, x| d.sub(succ_add_ja, x));
            let mid2 = d.sub(succ_add_ja, succ_add_jb);
            let step_ab = d.trans(sub_lhs, mid1, mid2, step_a, step_b);

            // succ_sub_succ(add_ja, add_jb) : Eq (sub (succ add_ja)(succ add_jb)) (sub add_ja add_jb)
            let h3 = d.lemma(p.succ_sub_succ, &[add_ja, add_jb]);
            let sub_ja_jb = d.sub(add_ja, add_jb);
            let step_c = d.trans(sub_lhs, mid2, sub_ja_jb, step_ab, h3);

            // ih : ∀ a b, Eq (sub (add j a)(add j b)) (sub a b) -- apply at (a, b).
            let ih_ab = d.apply(ih, &[a, b]);
            let proof_body = d.trans(sub_lhs, sub_ja_jb, sub_rhs, step_c, ih_ab);
            let nat2 = d.nat_ty();
            let inner = d.lam_fv(b_fv, nat2, proof_body);
            d.lam_fv(a_fv, nat2, inner)
        };

        let proof_fn = d.induct(&statement, &base, &step, k);
        let applied = d.apply(proof_fn, &[n, m]);

        let add_kn = d.add(k, n);
        let add_km = d.add(k, m);
        let sub_lhs = d.sub(add_kn, add_km);
        let sub_rhs = d.sub(n, m);
        (d.eq(sub_lhs, sub_rhs), applied)
    })?;
    Ok(())
}

/// `Nat.dist_add_add_left : ∀ k n m, Eq (dist (add k n) (add k m)) (dist n m)`
/// — `dist(k+n,k+m)` and `dist(n,m)` are both `add` of the SAME two truncated
/// subtractions after `add_sub_add_left` rewrites each, in the right order
/// (`sub(k+n,k+m) -> sub(n,m)`, then `sub(k+m,k+n) -> sub(m,n)`).
fn declare_dist_add_add_left(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.dist_add_add_left, 3, &|d, v| {
        let (k, n, m) = (v[0], v[1], v[2]);
        let add_kn = d.add(k, n);
        let add_km = d.add(k, m);
        let dist_kn_km = d.const_app(p.dist, &[add_kn, add_km]);
        let dist_nm = d.const_app(p.dist, &[n, m]);
        let stmt = d.eq(dist_kn_km, dist_nm);

        let sub_kn_km = d.sub(add_kn, add_km);
        let sub_km_kn = d.sub(add_km, add_kn);
        let sub_nm = d.sub(n, m);
        let sub_mn = d.sub(m, n);

        let h1 = d.lemma(p.add_sub_add_left, &[k, n, m]); // Eq sub_kn_km sub_nm
        let h2 = d.lemma(p.add_sub_add_left, &[k, m, n]); // Eq sub_km_kn sub_mn

        let step_a = d.congr(sub_kn_km, sub_nm, h1, &|d, x| d.add(x, sub_km_kn));
        let mid = d.add(sub_nm, sub_km_kn);
        let step_b = d.congr(sub_km_kn, sub_mn, h2, &|d, x| d.add(sub_nm, x));
        let proof = d.trans(dist_kn_km, mid, dist_nm, step_a, step_b);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Nat.dist_add_add_right : ∀ n k m, Eq (dist (add n k) (add m k)) (dist n m)`
/// — via `add_comm` rewriting both operands to `dist_add_add_left`'s shape
/// (`add n k = add k n`, `add m k = add k m`); no new arithmetic beyond that.
fn declare_dist_add_add_right(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.dist_add_add_right, 3, &|d, v| {
        let (n, k, m) = (v[0], v[1], v[2]);
        let add_nk = d.add(n, k);
        let add_mk = d.add(m, k);
        let dist_nk_mk = d.const_app(p.dist, &[add_nk, add_mk]);
        let dist_nm = d.const_app(p.dist, &[n, m]);
        let stmt = d.eq(dist_nk_mk, dist_nm);

        let add_kn = d.add(k, n);
        let add_km = d.add(k, m);

        let h_nk = d.lemma(p.add_comm, &[n, k]); // Eq (add n k) (add k n)
        let h_mk = d.lemma(p.add_comm, &[m, k]); // Eq (add m k) (add k m)

        let step_a = d.congr(add_nk, add_kn, h_nk, &|d, x| d.const_app(p.dist, &[x, add_mk]));
        let mid1 = d.const_app(p.dist, &[add_kn, add_mk]);
        let step_b = d.congr(add_mk, add_km, h_mk, &|d, x| d.const_app(p.dist, &[add_kn, x]));
        let mid2 = d.const_app(p.dist, &[add_kn, add_km]);
        let step_ab = d.trans(dist_nk_mk, mid1, mid2, step_a, step_b);

        let h_left = d.lemma(p.dist_add_add_left, &[k, n, m]); // Eq (dist (add k n)(add k m)) (dist n m)
        let proof = d.trans(dist_nk_mk, mid2, dist_nm, step_ab, h_left);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Nat.dist_mul_left : ∀ k n m, Eq (dist (mul k n) (mul k m)) (mul k (dist n m))`
/// — via `mul_sub_left_distrib_total` on both truncated subtractions
/// `dist` sums, then `left_distrib` to recombine `mul k (dist n m)`
/// (`dist n m` unfolds definitionally to `add (sub n m) (sub m n)`, so the
/// stated conclusion is defeq to `left_distrib`'s RHS-expanded form).
fn declare_dist_mul_left(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.dist_mul_left, 3, &|d, v| {
        let (k, n, m) = (v[0], v[1], v[2]);
        let mul_kn = d.mul(k, n);
        let mul_km = d.mul(k, m);
        let dist_kn_km = d.const_app(p.dist, &[mul_kn, mul_km]);
        let dist_nm = d.const_app(p.dist, &[n, m]);
        let mul_k_dist_nm = d.mul(k, dist_nm);
        let stmt = d.eq(dist_kn_km, mul_k_dist_nm);

        let sub_kn_km = d.sub(mul_kn, mul_km);
        let sub_km_kn = d.sub(mul_km, mul_kn);
        let sub_nm = d.sub(n, m);
        let sub_mn = d.sub(m, n);
        let mul_k_sub_nm = d.mul(k, sub_nm);
        let mul_k_sub_mn = d.mul(k, sub_mn);

        // mul_sub_left_distrib_total(k, n, m) : Eq (mul k (sub n m)) (sub (mul k n)(mul k m))
        let h1 = d.lemma(p.mul_sub_left_distrib_total, &[k, n, m]);
        let h1r = d.symm(mul_k_sub_nm, sub_kn_km, h1); // Eq sub_kn_km mul_k_sub_nm
        // mul_sub_left_distrib_total(k, m, n) : Eq (mul k (sub m n)) (sub (mul k m)(mul k n))
        let h2 = d.lemma(p.mul_sub_left_distrib_total, &[k, m, n]);
        let h2r = d.symm(mul_k_sub_mn, sub_km_kn, h2); // Eq sub_km_kn mul_k_sub_mn

        let step_a = d.congr(sub_kn_km, mul_k_sub_nm, h1r, &|d, x| d.add(x, sub_km_kn));
        let mid1 = d.add(mul_k_sub_nm, sub_km_kn);
        let step_b = d.congr(sub_km_kn, mul_k_sub_mn, h2r, &|d, x| d.add(mul_k_sub_nm, x));
        let mid2 = d.add(mul_k_sub_nm, mul_k_sub_mn);
        let step_ab = d.trans(dist_kn_km, mid1, mid2, step_a, step_b);

        // left_distrib(k, sub_nm, sub_mn) : Eq (mul k (add sub_nm sub_mn)) (add (mul k sub_nm)(mul k sub_mn))
        let add_nm_mn = d.add(sub_nm, sub_mn);
        let mul_k_add = d.mul(k, add_nm_mn);
        let h3 = d.lemma(p.left_distrib, &[k, sub_nm, sub_mn]);
        let h3r = d.symm(mul_k_add, mid2, h3); // Eq mid2 mul_k_add
        // mul_k_add is defeq to mul_k_dist_nm (dist n m unfolds to add sub_nm sub_mn).
        let proof = d.trans(dist_kn_km, mid2, mul_k_dist_nm, step_ab, h3r);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Nat.dist_mul_right : ∀ n k m, Eq (dist (mul n k) (mul m k)) (mul (dist n m) k)`
/// — via `mul_comm` rewriting both operands to `dist_mul_left`'s shape, then
/// `mul_comm` again on the conclusion (`mul k (dist n m) = mul (dist n m) k`).
fn declare_dist_mul_right(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.dist_mul_right, 3, &|d, v| {
        let (n, k, m) = (v[0], v[1], v[2]);
        let nk = d.mul(n, k);
        let mk = d.mul(m, k);
        let dist_nk_mk = d.const_app(p.dist, &[nk, mk]);
        let dist_nm = d.const_app(p.dist, &[n, m]);
        let dist_nm_k = d.mul(dist_nm, k);
        let stmt = d.eq(dist_nk_mk, dist_nm_k);

        let kn = d.mul(k, n);
        let km = d.mul(k, m);

        let h_nk = d.lemma(p.mul_comm, &[n, k]); // Eq (mul n k) (mul k n)
        let h_mk = d.lemma(p.mul_comm, &[m, k]); // Eq (mul m k) (mul k m)

        let step_a = d.congr(nk, kn, h_nk, &|d, x| d.const_app(p.dist, &[x, mk]));
        let mid1 = d.const_app(p.dist, &[kn, mk]);
        let step_b = d.congr(mk, km, h_mk, &|d, x| d.const_app(p.dist, &[kn, x]));
        let mid2 = d.const_app(p.dist, &[kn, km]);
        let step_ab = d.trans(dist_nk_mk, mid1, mid2, step_a, step_b);

        // dist_mul_left(k, n, m) : Eq (dist (mul k n)(mul k m)) (mul k (dist n m))
        let h_left = d.lemma(p.dist_mul_left, &[k, n, m]);
        let k_dist_nm = d.mul(k, dist_nm);
        let step_c = d.trans(dist_nk_mk, mid2, k_dist_nm, step_ab, h_left);

        let h_comm_final = d.lemma(p.mul_comm, &[k, dist_nm]); // Eq (mul k dist_nm) (mul dist_nm k)
        let proof = d.trans(dist_nk_mk, k_dist_nm, dist_nm_k, step_c, h_comm_final);
        (stmt, proof)
    })?;
    Ok(())
}

/// Declare [`declare_dist_eq_zero`], [`declare_add_sub_add_left`],
/// [`declare_dist_add_add_left`], [`declare_dist_add_add_right`],
/// [`declare_dist_mul_left`] and [`declare_dist_mul_right`] — the draw-9
/// (`natural-distance`, ADR-0830) additions to `Nat.dist`, filed separately
/// from `declare_dist_all` so the original seven-theorem lane's set stays
/// intact and reviewable on its own.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_dist_more_all(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    declare_dist_eq_zero(d, p)?;
    declare_add_sub_add_left(d, p)?;
    declare_dist_add_add_left(d, p)?;
    declare_dist_add_add_right(d, p)?;
    declare_dist_mul_left(d, p)?;
    declare_dist_mul_right(d, p)?;
    Ok(())
}
