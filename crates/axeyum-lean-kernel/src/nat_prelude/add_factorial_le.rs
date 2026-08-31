//! `Nat.add_factorial_le_factorial_add : ∀ i {n}, 1 ≤ n → i + n! ≤ (i+n)!`
//! -- an `ml430` mirror (`F:ml430-nat-add-factorial-le-factorial-add-b0400cf6`)
//! -- and its unconditional-in-`n` corollary
//! `Nat.add_factorial_succ_le_factorial_add_succ : ∀ i n, i + (n+1)! ≤
//! (i+(n+1))!` (`F:ml430-nat-add-factorial-succ-le-factorial-add-succ-e8145feb`,
//! immediate from the first at `n := succ n` via [`NatOps::zero_lt_succ`]).
//!
//! Proved by induction on `i`, `n` (and the hypothesis `1 ≤ n`) held fixed.
//! Writing `F := (i+n)!`:
//!
//! - Base (`i = 0`): both sides collapse to `n!` via `zero_add` (`Nat.add`
//!   recurses on its RIGHT argument, so `0 + x` is stuck for symbolic `x` and
//!   needs the real theorem, not `refl`); `le_refl` closes it.
//! - Step (`i = succ j`, `ih : j + n! ≤ F`): `succ j + n!` is `succ(j+n!)`
//!   via `succ_add` (again a real rewrite, `succ` is on the LEFT). The goal's
//!   RHS, `(succ j + n)!`, is `factorial (succ (j+n))` after the same
//!   `succ_add` rewrite on its argument, and THAT is `Eq.refl`-defeq to
//!   `mul F (j+n) + F` (`factorial_succ` is itself proved by `refl` --
//!   `defs.rs` -- and `mul` recurses on its right argument same as `add`),
//!   so no further lemma names that unfolding. So the goal reduces to
//!   showing `succ (j+n!) ≤ mul F (j+n) + F`:
//!   - `le_succ_succ(ih)` gives `succ(j+n!) ≤ succ F`.
//!   - `succ F` (defeq `F+1`) `≤ F + mul F (j+n)` needs only
//!     `add_le_add_left` against `1 ≤ mul F (j+n)`, itself
//!     `one_le_mul(one_le_factorial(j+n), one_le_of(1 ≤ n ≤ j+n))`
//!     (`n ≤ j+n` via `le_add_right` + `add_comm`, then `le_trans` with the
//!     hypothesis).
//!   - `add_comm` swaps `F + mul F (j+n)` to `mul F (j+n) + F`, and
//!     `le_trans` chains the two `≤` steps.
//!   Two local helpers (`le_transport_lhs`/`le_transport_rhs`) thread the
//!   `succ_add` rewrites back onto the goal's exact shape at the end.

use super::NatPrelude;
use super::ops::{NatDev, NatOps};
use crate::KernelError;
use crate::expr::ExprId;

/// Given `proof : Le a b1` and `eq_b1_b2 : Eq b1 b2`, build `Le a b2`.
fn le_transport_rhs(
    d: &mut NatDev<'_>,
    a: ExprId,
    b1: ExprId,
    b2: ExprId,
    eq_b1_b2: ExprId,
    proof: ExprId,
) -> ExprId {
    let motive = d.eq_motive(b1, &|d, x| d.le(a, x));
    d.transport(b1, motive, proof, b2, eq_b1_b2)
}

/// Given `proof : Le a1 b` and `eq_a1_a2 : Eq a1 a2`, build `Le a2 b`.
fn le_transport_lhs(
    d: &mut NatDev<'_>,
    a1: ExprId,
    a2: ExprId,
    b: ExprId,
    eq_a1_a2: ExprId,
    proof: ExprId,
) -> ExprId {
    let motive = d.eq_motive(a1, &|d, x| d.le(x, b));
    d.transport(a1, motive, proof, a2, eq_a1_a2)
}

/// `Nat.add_factorial_le_factorial_add`: `∀ i n, Le 1 n → Le (i + n!)
/// ((i+n)!)`. See the module doc for the route.
pub(super) fn declare_add_factorial_le_factorial_add(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.add_factorial_le_factorial_add, 2, &|d, v| {
        let (i, n) = (v[0], v[1]);
        let nfact = d.factorial(n);
        let one = d.num(1);
        let hyp_ty = d.le(one, n);

        let motive = |d: &mut NatDev<'_>, x: ExprId| -> ExprId {
            let lhs = d.add(x, nfact);
            let add_xn = d.add(x, n);
            let rhs = d.factorial(add_xn);
            d.le(lhs, rhs)
        };
        let stmt_body = motive(d, i);
        let stmt = d.arrow(hyp_ty, stmt_body);

        let hyp_fv = d.fresh_fvar();
        let hyp = d.kernel().fvar(hyp_fv);

        let base = |d: &mut NatDev<'_>| -> ExprId {
            let zero = d.zero();
            let z_lhs_eq = d.lemma(p.zero_add, &[nfact]); // Eq(add(zero,nfact), nfact)
            let z_rhs_eq = d.lemma(p.zero_add, &[n]); // Eq(add(zero,n), n)
            let base0 = d.lemma(p.le_refl, &[nfact]); // Le(nfact,nfact)

            let zero_n = d.add(zero, n);
            let z_rhs_eq_rev = d.symm(zero_n, n, z_rhs_eq); // Eq(n, add(zero,n))
            let rhs_base = d.factorial(zero_n);
            let rhs_cong = d.congr(n, zero_n, z_rhs_eq_rev, &|d, x| d.factorial(x)); // Eq(nfact, rhs_base)
            let after_rhs = le_transport_rhs(d, nfact, nfact, rhs_base, rhs_cong, base0);

            let zero_nfact = d.add(zero, nfact);
            let z_lhs_eq_rev = d.symm(zero_nfact, nfact, z_lhs_eq); // Eq(nfact, add(zero,nfact))
            le_transport_lhs(d, nfact, zero_nfact, rhs_base, z_lhs_eq_rev, after_rhs)
        };

        let step = |d: &mut NatDev<'_>, j: ExprId, ih: ExprId| -> ExprId {
            let one = d.num(1);
            let sj = d.succ(j);
            let j_nfact = d.add(j, nfact);
            let in_j = d.add(j, n);
            let ffact = d.factorial(in_j);

            // sa1 : Eq(add(sj,nfact), succ(j_nfact))
            let sa1 = d.lemma(p.succ_add, &[j, nfact]);
            let lhs_orig = d.add(sj, nfact);
            let lhs_new = d.succ(j_nfact);

            // sa2 : Eq(add(sj,n), succ(in_j))
            let sa2 = d.lemma(p.succ_add, &[j, n]);
            let sj_n = d.add(sj, n);
            let rhs_orig = d.factorial(sj_n);
            let succ_in_j = d.succ(in_j);
            let rhs_new = d.factorial(succ_in_j); // defeq add(mul(ffact,in_j), ffact)
            let rhs_new_eq = d.congr(sj_n, succ_in_j, sa2, &|d, x| d.factorial(x)); // Eq(rhs_orig, rhs_new)

            // step1 : Le(succ(j_nfact), succ(ffact)) = Le(lhs_new, succ(ffact))
            let step1 = d.lemma(p.le_succ_succ, &[j_nfact, ffact, ih]);

            // one_le_in_j : Le(1, in_j)
            let n_j = d.add(n, j);
            let le_n_addnj = d.lemma(p.le_add_right, &[n, j]); // Le(n, add(n,j))
            let comm_nj = d.lemma(p.add_comm, &[n, j]); // Eq(add(n,j), in_j)
            let le_n_inj = le_transport_rhs(d, n, n_j, in_j, comm_nj, le_n_addnj); // Le(n, in_j)
            let one_le_inj = d.lemma(p.le_trans, &[one, n, in_j, hyp, le_n_inj]); // Le(1, in_j)

            let one_le_ffact = d.lemma(p.one_le_factorial, &[in_j]); // Le(1, ffact)
            let mul_f_inj = d.mul(ffact, in_j);
            let one_le_prod = d.lemma(p.one_le_mul, &[ffact, in_j, one_le_ffact, one_le_inj]); // Le(1, mul_f_inj)

            let ffact_one = d.add(ffact, one);
            let growth0 = d.lemma(p.add_le_add_left, &[ffact, one, mul_f_inj, one_le_prod]);
            // growth0 : Le(ffact_one, add(ffact, mul_f_inj))

            let add_f_mul = d.add(ffact, mul_f_inj);
            let add_mul_f = d.add(mul_f_inj, ffact);
            let comm_growth = d.lemma(p.add_comm, &[mul_f_inj, ffact]); // Eq(add_mul_f, add_f_mul)
            let comm_growth_rev = d.symm(add_mul_f, add_f_mul, comm_growth); // Eq(add_f_mul, add_mul_f)
            let growth = le_transport_rhs(d, ffact_one, add_f_mul, add_mul_f, comm_growth_rev, growth0);
            // growth : Le(ffact_one, add_mul_f) -- defeq Le(succ(ffact), add_mul_f)

            let succ_ffact = d.succ(ffact);
            let core = d.lemma(p.le_trans, &[lhs_new, succ_ffact, add_mul_f, step1, growth]);
            // core : Le(lhs_new, add_mul_f) -- defeq Le(lhs_new, rhs_new)

            let rhs_new_eq_rev = d.symm(rhs_orig, rhs_new, rhs_new_eq); // Eq(rhs_new, rhs_orig)
            let after_rhs = le_transport_rhs(d, lhs_new, rhs_new, rhs_orig, rhs_new_eq_rev, core);

            let sa1_rev = d.symm(lhs_orig, lhs_new, sa1); // Eq(lhs_new, lhs_orig)
            le_transport_lhs(d, lhs_new, lhs_orig, rhs_orig, sa1_rev, after_rhs)
        };

        let body = d.induct(&motive, &base, &step, i);
        let proof = d.lam_fv(hyp_fv, hyp_ty, body);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Nat.add_factorial_succ_le_factorial_add_succ`: `∀ i n, Le (i + (succ
/// n)!) ((i + succ n)!)`. Immediate corollary of
/// [`declare_add_factorial_le_factorial_add`] at `n := succ n`, discharging
/// its `Le 1 (succ n)` hypothesis with [`NatOps::zero_lt_succ`].
pub(super) fn declare_add_factorial_succ_le_factorial_add_succ(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.add_factorial_succ_le_factorial_add_succ, 2, &|d, v| {
        let (i, n) = (v[0], v[1]);
        let sn = d.succ(n);
        let hyp = d.zero_lt_succ(n); // Le 1 (succ n)
        let proof = d.lemma(p.add_factorial_le_factorial_add, &[i, sn, hyp]);

        let fact_sn = d.factorial(sn);
        let lhs = d.add(i, fact_sn);
        let i_sn = d.add(i, sn);
        let rhs = d.factorial(i_sn);
        let stmt = d.le(lhs, rhs);
        (stmt, proof)
    })?;
    Ok(())
}
