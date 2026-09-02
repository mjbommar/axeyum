//! `Rat.det_row_selection_of_duplicate` — the FREE half of the SELECTION
//! lemma (ADR-1440 obligation 2), the last obstruction to
//! `det (A*B) = det A * det B` at symbolic `n`.
//!
//! ## The statement is not what it looks like
//!
//! The naive target `det (B o g) n = det (matId o g) n * det B n`, with `g`
//! totally unrestricted, is FALSE. Counterexample: `n=1`, `g 0 = 5`,
//! `B 5 0 = 7`. Then `det (B o g) 1 = B 5 0 = 7` (by `det_one`), while
//! `det (matId o g) 1 = matId 5 0 = 0` (`5 != 0`) so the right side is `0`.
//! `7 != 0`.
//!
//! The correct, general statement needs `MapsInto g n` (`g` sends `[0,n)`
//! into `[0,n)`). `InjectiveOn g n` is NOT an extra hypothesis on the final
//! theorem: when `g` is not injective on `[0,n)`, both sides are `0` for
//! free (`Rat.det_alternating`, since two rows of `B o g` and of
//! `matId o g` coincide) -- but `MapsInto` cannot be dropped, because the
//! injective-and-not-onto case (the counterexample above) is exactly where
//! it fails.
//!
//! ## What this file proves
//!
//! Exactly the free half: given an EXPLICIT duplicate pair `i != j` with
//! `g i = g j` (both in range), both sides are `0` and the equation holds
//! trivially. This needs no `MapsInto` at all -- `det_alternating` only
//! needs two equal rows, regardless of what value they equal.
//!
//! `Rat.det_row_selection_of_duplicate`, stated at dimension `succ m`
//! (matching `Rat.det_alternating`'s own convention, so its hypotheses pass
//! straight through with no bridging):
//!
//! ```text
//! ∀ m B g i j,
//!   Nat.beq i j = false → Nat.ble i m = true → Nat.ble j m = true →
//!   Eq Nat (g i) (g j) →
//!   det (fun r c => B (g r) c) (succ m)
//!     = det (fun r c => matId (g r) c) (succ m) * det B (succ m)
//! ```
//!
//! ## What this file does NOT prove
//!
//! The injective case -- ADR-1440's "the real one" -- needs a cursor
//! induction (pigeonhole via `Nat.injective_on_imp_surjective_on`, a 2-point
//! swap composed with `g` via `Nat.injective_on_comp`, and `Rat.det_row_swap`
//! to relate `det (B o (g o swap))` to `det (B o g)`). That combinatorial
//! argument, and a bounded-search decidability construction for
//! `InjectiveOn g n \/ (duplicate)` (nothing in-tree gives this), are NOT
//! attempted here -- see `ADR-1470` for the fully worked-out route and why
//! it did not land this lane.
//!
//! Neither is `Rat.det_matId` combined with the full theorem to recover
//! `det (A*B) n = det A n * det B n`; that assembly is `ADR-1440`'s
//! "obligation 1 + obligation 2", still open on obligation 2's injective
//! half.

use super::RatPrelude;
use super::matrix_det::{alt_hyp_ne, ble_true_ty, mat_ty, rdet, rmat_id};
use super::ops::{nat_eq_to_rat, rchain, rcongr, rmul, rsymm, rtrans, rzero};
use crate::KernelError;
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::NatOps;

/// `fun r c => mat (g r) c` -- a matrix's rows reindexed by `g`. A pure
/// Rust-level term builder, never a registered kernel `Definition`, matching
/// this prelude's convention (`matrix_det.rs`'s module doc): `funext` is
/// absent, so no statement here is an `Eq` between two `Nat -> Nat -> Rat`
/// values, and nothing downstream needs this to have a name.
pub(super) fn row_compose(d: &mut IntDev<'_>, mat: ExprId, g: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let r_fv = d.fresh_fvar();
    let r = d.kernel().fvar(r_fv);
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let gr = d.apply(g, &[r]);
    let body = d.apply(mat, &[gr, c]);
    let inner = d.lam_fv(c_fv, nat, body);
    d.lam_fv(r_fv, nat, inner)
}

/// `heq : Eq Nat (g i) (g j) ⊢ ∀ c, mat (g i) c = mat (g j) c` -- the
/// pointwise row-equality hypothesis `Rat.det_alternating` needs, at the
/// matrix `row_compose(mat, g)`, i.e. the same statement up to `row_compose`'s
/// (beta-only) unfolding.
fn row_eq_from_g_eq(
    d: &mut IntDev<'_>,
    mat: ExprId,
    g: ExprId,
    i: ExprId,
    j: ExprId,
    heq: ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let gi = d.apply(g, &[i]);
    let gj = d.apply(g, &[j]);
    let step = nat_eq_to_rat(d, gi, gj, heq, &|d, t| d.apply(mat, &[t, c]));
    d.lam_fv(c_fv, nat, step)
}

/// `Eq Rat (Rat.mul Rat.zero x) Rat.zero` -- this prelude has no `zero_mul`,
/// so it is `mul_comm` followed by `mul_zero`.
fn zero_mul_pf(d: &mut IntDev<'_>, p: RatPrelude, x: ExprId) -> ExprId {
    let zero_r = rzero(d, p);
    let zero_x = rmul(d, zero_r, x);
    let x_zero = rmul(d, x, zero_r);
    let comm = d.lemma(p.mul_comm, &[zero_r, x]);
    let mz = d.lemma(p.mul_zero, &[x]);
    rtrans(d, zero_x, x_zero, zero_r, comm, mz)
}

/// The proof body of `Rat.det_row_selection_of_duplicate` at fixed
/// `m, B, g, i, j` and the four hypotheses -- see the module doc for the
/// statement and the argument (`det_alternating` on both reindexed matrices,
/// then `0 = 0 * det B (succ m)` via `mul_comm` + `mul_zero`).
#[allow(clippy::too_many_arguments)]
fn selection_of_duplicate_body(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    m: ExprId,
    b_mat: ExprId,
    g: ExprId,
    i: ExprId,
    j: ExprId,
    hne: ExprId,
    hbi: ExprId,
    hbj: ExprId,
    heq: ExprId,
) -> ExprId {
    let sm = d.succ(m);
    let bc_mat = row_compose(d, b_mat, g);
    let mid_term = rmat_id(d, p);
    let mi_mat = row_compose(d, mid_term, g);

    let bc_row_eq = row_eq_from_g_eq(d, b_mat, g, i, j, heq);
    let mi_row_eq = row_eq_from_g_eq(d, mid_term, g, i, j, heq);

    let det_bc_zero = d.const_app(
        p.det_alternating,
        &[m, bc_mat, i, j, hne, hbi, hbj, bc_row_eq],
    );
    let det_mi_zero = d.const_app(
        p.det_alternating,
        &[m, mi_mat, i, j, hne, hbi, hbj, mi_row_eq],
    );

    let det_b_n = rdet(d, p, b_mat, sm);
    let det_mi_val = rdet(d, p, mi_mat, sm);
    let zero_r = rzero(d, p);
    let rhs_before = rmul(d, det_mi_val, det_b_n);
    let zero_x = rmul(d, zero_r, det_b_n);
    let step1 = rcongr(d, det_mi_val, zero_r, det_mi_zero, &|d, t| {
        rmul(d, t, det_b_n)
    });
    let zm = zero_mul_pf(d, p, det_b_n);
    let (_e, rhs_eq_zero) = rchain(d, rhs_before, &[(zero_x, step1), (zero_r, zm)]);

    let det_bc = rdet(d, p, bc_mat, sm);
    let rhs_eq_zero_symm = rsymm(d, rhs_before, zero_r, rhs_eq_zero);
    rtrans(d, det_bc, zero_r, rhs_before, det_bc_zero, rhs_eq_zero_symm)
}

/// Admit `Rat.det_row_selection_of_duplicate` -- see the module doc for the
/// statement, the argument, and what remains (`ADR-1470`).
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_det_row_selection(
    d: &mut IntDev<'_>,
    p: RatPrelude,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let mty = mat_ty(d);

    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let b_fv = d.fresh_fvar();
    let b_mat = d.kernel().fvar(b_fv);
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);

    let hne_ty = alt_hyp_ne(d, i, j);
    let hbi_ty = ble_true_ty(d, i, m);
    let hbj_ty = ble_true_ty(d, j, m);
    let gi = d.apply(g, &[i]);
    let gj = d.apply(g, &[j]);
    let heq_ty = d.eq(gi, gj);

    let sm = d.succ(m);
    let bc_mat_ty = row_compose(d, b_mat, g);
    let mid_term_ty = rmat_id(d, p);
    let mi_mat_ty = row_compose(d, mid_term_ty, g);
    let det_bc_ty = rdet(d, p, bc_mat_ty, sm);
    let det_mi_ty = rdet(d, p, mi_mat_ty, sm);
    let det_b_ty = rdet(d, p, b_mat, sm);
    let rhs_ty = rmul(d, det_mi_ty, det_b_ty);
    let concl_ty = super::ops::req(d, det_bc_ty, rhs_ty);

    let arr = d.arrow(heq_ty, concl_ty);
    let arr = d.arrow(hbj_ty, arr);
    let arr = d.arrow(hbi_ty, arr);
    let arr = d.arrow(hne_ty, arr);
    let over_j = d.pi_fv(j_fv, nat, arr);
    let over_i = d.pi_fv(i_fv, nat, over_j);
    let fn_ty = d.arrow(nat, nat);
    let over_g = d.pi_fv(g_fv, fn_ty, over_i);
    let over_b = d.pi_fv(b_fv, mty, over_g);
    let ty = d.pi_fv(m_fv, nat, over_b);

    let hne_fv = d.fresh_fvar();
    let hne = d.kernel().fvar(hne_fv);
    let hbi_fv = d.fresh_fvar();
    let hbi = d.kernel().fvar(hbi_fv);
    let hbj_fv = d.fresh_fvar();
    let hbj = d.kernel().fvar(hbj_fv);
    let heq_fv = d.fresh_fvar();
    let heq = d.kernel().fvar(heq_fv);

    let body = selection_of_duplicate_body(d, p, m, b_mat, g, i, j, hne, hbi, hbj, heq);

    let value = d.lam_fv(heq_fv, heq_ty, body);
    let value = d.lam_fv(hbj_fv, hbj_ty, value);
    let value = d.lam_fv(hbi_fv, hbi_ty, value);
    let value = d.lam_fv(hne_fv, hne_ty, value);
    let value = d.lam_fv(j_fv, nat, value);
    let value = d.lam_fv(i_fv, nat, value);
    let value = d.lam_fv(g_fv, fn_ty, value);
    let value = d.lam_fv(b_fv, mty, value);
    let value = d.lam_fv(m_fv, nat, value);

    d.declare_theorem(p.det_row_selection_of_duplicate, ty, value)
}
