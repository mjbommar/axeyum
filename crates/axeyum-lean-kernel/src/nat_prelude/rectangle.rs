//! `rectangle = triangle + corner` over ℕ — the identity that makes a finite
//! Cauchy product statable at all.
//!
//! # The refutation this module answers
//!
//! The naive finite Cauchy identity
//! `(Σ_{i<n} a i)·(Σ_{j<n} b j) = Σ_{k<n} Σ_{i≤k} a i · b (k−i)` is FALSE: at
//! `n = 2` the left side is `a0 b0 + a0 b1 + a1 b0 + a1 b1` and the right is
//! `a0 b0 + (a0 b1 + a1 b0)`, differing by `a1 b1`. The pair `(1,1)` is in the
//! RECTANGLE `{i<2, j<2}` and outside the TRIANGLE `{i+j<2}`; for every
//! `n ≥ 2` the rectangle strictly contains that antidiagonal-bounded triangle.
//! So the honest finite statement is a three-way decomposition, not a
//! two-way equation: `rectangle = triangle + corner`, where `corner` is the
//! sum over `{(i,j) : i<n, j<n, i+j ≥ n}` — the part of the square the
//! antidiagonal triangle misses.
//!
//! # The corner, parametrized without nested subtraction
//!
//! Row `i`'s full width is `Σ_{j<n} F i j`. [`super::diagonal`] already
//! reindexes the PREFIX `Σ_{j<n−i} F i j` (`row_fn`/`row_sum`) against the
//! antidiagonal triangle via `sumRange_diagonal`. What is left over in row
//! `i` is exactly the SUFFIX of width `i`: reindexing `j := (n−i)+k` for
//! `k < i` gives `Σ_{k<i} F i ((n−i)+k)` — one subtraction (`n−i`), never
//! nested, because the suffix's own reindexing shift `n−i` is added to `k`,
//! not subtracted again. This is [`declare_sum_range_split`] applied at the
//! split point `m := n−i`, `j := i`, using `Nat.sub_add_cancel` to rewrite
//! the row's bound `n` as `(n−i)+i` before splitting — the same round-trip
//! lemma [`super::diagonal`]'s module doc names as the piece
//! `add_sub_cancel_of_le` complements.
//!
//! `Nat.sumRange_split` is new here (ℝ and ℂ already have it —
//! `CRealPrelude::sum_range_split`, `ComplexPrelude::sum_range_split` — ℕ did
//! not); it is quantified over the split point `m` and the tail length `j`
//! directly (`bound := m+j`), the same shape `Rat.prob_complement`'s private
//! `sum_range_split` uses and for the same reason: induction on `j` alone,
//! `f` and `m` held fixed, aligns with `Nat.add`'s own recursion
//! (`add m (succ j) ≡ succ (add m j)`) for free, so the proof never touches
//! `Nat.sub`.
//!
//! # The headline: `Nat.sumRange_rect_eq_diag_add_corner`
//!
//! [`declare_sum_range_rect_eq_diag_add_corner`] states
//! `Σ_{i<n} Σ_{j<n} F i j = (Σ_{k<n} Σ_{i≤k} F i (k−i)) + Σ_{i<n} Σ_{k<i} F i
//! ((n−i)+k)` — rectangle = (antidiagonal triangle) + corner — by: split
//! every row via [`declare_sum_range_split`] (pointwise, for `i < n`, via
//! `sumRange_congr_lt`), regroup the two halves via `sumRange_add`, then
//! replace the row-major half by the antidiagonal triangle via
//! [`super::diagonal::declare_sum_range_diagonal`]'s own headline.

use super::NatPrelude;
use super::diagonal::{combined_fn, row_fn, row_inner, row_sum, triangle_sum};
use super::ops::{NatDev, NatOps};
use crate::KernelError;
use crate::expr::ExprId;

// ---------------------------------------------------------------------------
// `Nat.sumRange_split`.
// ---------------------------------------------------------------------------

/// `fun k => f (add m k)` — `f` shifted so its own zero sits at `m`.
fn shifted(d: &mut NatDev<'_>, f: ExprId, m: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let mk = d.add(m, k);
    let fmk = d.apply(f, &[mk]);
    d.lam_fv(k_fv, nat, fmk)
}

/// `sumRange_split : ∀ f m j,
///   sumRange f (add m j) = add (sumRange f m) (sumRange (fun k => f (add m k)) j)`.
///
/// By induction on `j`, `f` and `m` held fixed — every step uses only
/// `Nat.add`'s and `Nat.sumRange`'s own defining (ι-rule) equations plus
/// `add_zero`/`add_assoc`, never `Nat.sub`.
pub(super) fn declare_sum_range_split(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let fn_ty = d.arrow(nat, nat);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);

    let g = shifted(d, f, m);
    let sum_f_m = d.sum_range(f, m);

    let motive = |d: &mut NatDev<'_>, x: ExprId| -> ExprId {
        let bound = d.add(m, x);
        let lhs = d.sum_range(f, bound);
        let tail = d.sum_range(g, x);
        let rhs = d.add(sum_f_m, tail);
        d.eq(lhs, rhs)
    };
    let stmt = motive(d, j);

    let proof = d.induct(
        &motive,
        &|d| {
            let zero = d.zero();
            let rhs = d.add(sum_f_m, zero);
            // add_zero sum_f_m : Eq(add sum_f_m zero, sum_f_m); flip it.
            let h = d.lemma(p.add_zero, &[sum_f_m]);
            d.symm(rhs, sum_f_m, h)
        },
        &|d, k, ih| {
            // ih : Eq(sumRange f (add m k), add sum_f_m (sumRange g k))
            let mk = d.add(m, k);
            let f_mk = d.apply(f, &[mk]);
            let sum_f_mk = d.sum_range(f, mk);
            let sum_g_k = d.sum_range(g, k);
            let sum_f_m_g_k = d.add(sum_f_m, sum_g_k);

            // start ≡ sumRange f (add m (succ k)), by Nat.add's + sumRange's
            // own ι-rules.
            let start = d.add(sum_f_mk, f_mk);
            let mid = d.add(sum_f_m_g_k, f_mk);
            let h1 = d.congr(sum_f_mk, sum_f_m_g_k, ih, &|d, t| d.add(t, f_mk));

            let inner = d.add(sum_g_k, f_mk);
            let end = d.add(sum_f_m, inner);
            let h2 = d.lemma(p.add_assoc, &[sum_f_m, sum_g_k, f_mk]);

            let (_e, chained) = d.chain(start, &[(mid, h1), (end, h2)]);
            chained
        },
        j,
    );

    let ty = {
        let over_j = d.pi_fv(j_fv, nat, stmt);
        let over_m = d.pi_fv(m_fv, nat, over_j);
        d.pi_fv(f_fv, fn_ty, over_m)
    };
    let value = {
        let over_j = d.lam_fv(j_fv, nat, proof);
        let over_m = d.lam_fv(m_fv, nat, over_j);
        d.lam_fv(f_fv, fn_ty, over_m)
    };
    d.declare_theorem(p.sum_range_split, ty, value)
}

// ---------------------------------------------------------------------------
// The rectangle, and the corner.
// ---------------------------------------------------------------------------

/// `fun i => sumRange (fun j => F i j) n` — one row of the RECTANGLE sum, at
/// its full width `n` (unlike [`row_fn`], which stops at `n−i`).
fn rect_row(d: &mut NatDev<'_>, ff: ExprId, n: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let inner = row_inner(d, ff, i);
    let sr = d.sum_range(inner, n);
    d.lam_fv(i_fv, nat, sr)
}

/// The rectangle sum `Σ_{i<n} Σ_{j<n} F i j`.
fn rectangle_sum(d: &mut NatDev<'_>, ff: ExprId, n: ExprId) -> ExprId {
    let r = rect_row(d, ff, n);
    d.sum_range(r, n)
}

/// Row `i`'s corner summand: `shifted(row_inner F i, sub n i)`, i.e.
/// `fun k => F i (add (sub n i) k)` — the suffix of row `i` beyond the
/// `row_fn` prefix, reindexed to start at `0`.
fn corner_inner(d: &mut NatDev<'_>, ff: ExprId, i: ExprId, n: ExprId) -> ExprId {
    let row_inner_i = row_inner(d, ff, i);
    let sub_ni = d.sub(n, i);
    shifted(d, row_inner_i, sub_ni)
}

/// `fun i => sumRange (corner_inner F i n) i` — row `i`'s corner mass, width
/// `i` (row `i`'s full width `n` minus the `row_fn` prefix's width `n−i`).
fn corner_row(d: &mut NatDev<'_>, ff: ExprId, n: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let inner = corner_inner(d, ff, i, n);
    let sr = d.sum_range(inner, i);
    d.lam_fv(i_fv, nat, sr)
}

/// The corner sum `Σ_{i<n} Σ_{k<i} F i ((n−i)+k)`, i.e. the mass of
/// `{(i,j) : i<n, j<n, i+j ≥ n}`.
fn corner_sum(d: &mut NatDev<'_>, ff: ExprId, n: ExprId) -> ExprId {
    let c = corner_row(d, ff, n);
    d.sum_range(c, n)
}

/// `∀ i, Lt i n → Eq (sumRange (row_inner F i) n)
///   (add (sumRange (row_inner F i) (sub n i)) (sumRange (corner_inner F i n) i))`
/// — row `i`'s full width splits into the `row_fn` prefix and the corner
/// suffix, for `i < n` (hence `i ≤ n`, which [`Self::sum_range_split`]'s
/// split point `n = (n−i)+i` needs via `sub_add_cancel`).
fn rect_pointwise(d: &mut NatDev<'_>, p: &NatPrelude, ff: ExprId, n: ExprId) -> ExprId {
    let p = *p;
    let nat = d.nat_ty();

    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let hyp_ty = d.lt(i, n);
    let hi_fv = d.fresh_fvar();
    let hi = d.kernel().fvar(hi_fv);

    // Le i n, from Lt i n (definitionally Le (succ i) n) via le_succ + le_trans.
    let si = d.succ(i);
    let le_succ_i = d.lemma(p.le_succ, &[i]);
    let le_i_n = d.lemma(p.le_trans, &[i, si, n, le_succ_i, hi]);

    let row_inner_i = row_inner(d, ff, i);
    let sub_ni = d.sub(n, i);

    // sub_add_cancel i n le_i_n : add (sub n i) i = n
    let h_restore = d.lemma(p.sub_add_cancel, &[i, n, le_i_n]);
    let add_sub_i = d.add(sub_ni, i);
    let n_eq = d.symm(add_sub_i, n, h_restore);

    let sum_row_i_n = d.sum_range(row_inner_i, n);
    let sum_row_i_addsubi = d.sum_range(row_inner_i, add_sub_i);
    let h_lift = d.congr(n, add_sub_i, n_eq, &|d, x| d.sum_range(row_inner_i, x));

    let h_split = d.lemma(p.sum_range_split, &[row_inner_i, sub_ni, i]);

    let sum_row_i_subni = d.sum_range(row_inner_i, sub_ni);
    let corner_i = shifted(d, row_inner_i, sub_ni);
    let sum_corner_i = d.sum_range(corner_i, i);
    let rhs = d.add(sum_row_i_subni, sum_corner_i);

    let (_e, body) = d.chain(sum_row_i_n, &[(sum_row_i_addsubi, h_lift), (rhs, h_split)]);

    let with_hi = d.lam_fv(hi_fv, hyp_ty, body);
    d.lam_fv(i_fv, nat, with_hi)
}

/// `Eq (rectangle_sum F n) (add (row_sum F n) (corner_sum F n))` — split every
/// row (via [`rect_pointwise`] + `sumRange_congr_lt`), then regroup the two
/// halves (via `sumRange_add`).
fn rectangle_split_step(d: &mut NatDev<'_>, p: &NatPrelude, ff: ExprId, n: ExprId) -> ExprId {
    let p = *p;

    let rect_row_n = rect_row(d, ff, n);
    let row_fn_n = row_fn(d, ff, n);
    let corner_row_n = corner_row(d, ff, n);
    let combined = combined_fn(d, row_fn_n, corner_row_n);

    let pointwise = rect_pointwise(d, &p, ff, n);
    let h1 = d.lemma(p.sum_range_congr_lt, &[rect_row_n, combined, n, pointwise]);

    let h2 = d.lemma(p.sum_range_add, &[row_fn_n, corner_row_n, n]);

    let rect_sum = d.sum_range(rect_row_n, n);
    let sum_combined = d.sum_range(combined, n);
    let row_sum_n = d.sum_range(row_fn_n, n);
    let corner_sum_n = d.sum_range(corner_row_n, n);
    let final_rhs = d.add(row_sum_n, corner_sum_n);

    let (_e, proof) = d.chain(rect_sum, &[(sum_combined, h1), (final_rhs, h2)]);
    proof
}

/// `sumRange_rect_eq_diag_add_corner : ∀ F n,
///   sumRange (fun i => sumRange (fun j => F i j) n) n
///     = add (sumRange (fun k => sumRange (fun i => F i (sub k i)) (succ k)) n)
///           (sumRange (fun i => sumRange (fun k => F i (add (sub n i) k)) i) n)`
/// — rectangle = (antidiagonal triangle) + corner, the honest replacement for
/// the false naive finite Cauchy identity (see the module doc).
///
/// Route: [`rectangle_split_step`] gives rectangle = `row_sum` + `corner_sum`;
/// [`super::diagonal`]'s own `sumRange_diagonal` gives `row_sum` = `triangle_sum`
/// (symm'd); `trans` composes the two.
pub(super) fn declare_sum_range_rect_eq_diag_add_corner(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let fn2_ty = {
        let inner = d.arrow(nat, nat);
        d.arrow(nat, inner)
    };
    let f_fv = d.fresh_fvar();
    let ff = d.kernel().fvar(f_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let rect = rectangle_sum(d, ff, n);
    let tri = triangle_sum(d, ff, n);
    let corner = corner_sum(d, ff, n);
    let rhs_stmt = d.add(tri, corner);
    let stmt = d.eq(rect, rhs_stmt);

    let split_proof = rectangle_split_step(d, &p, ff, n);

    let row_sum_n = row_sum(d, ff, n);
    let corner_sum_n = corner_sum(d, ff, n);
    let mid = d.add(row_sum_n, corner_sum_n);

    // sum_range_diagonal ff n : Eq(triangle_sum, row_sum)  [T(n) = R(n)]
    let h_diag = d.lemma(p.sum_range_diagonal, &[ff, n]);
    let h_diag_symm = d.symm(tri, row_sum_n, h_diag);

    let h_lift = d.congr(row_sum_n, tri, h_diag_symm, &|d, x| d.add(x, corner_sum_n));

    let (_e, proof) = d.chain(rect, &[(mid, split_proof), (rhs_stmt, h_lift)]);

    let ty = {
        let over_n = d.pi_fv(n_fv, nat, stmt);
        d.pi_fv(f_fv, fn2_ty, over_n)
    };
    let value = {
        let over_n = d.lam_fv(n_fv, nat, proof);
        d.lam_fv(f_fv, fn2_ty, over_n)
    };
    d.declare_theorem(p.sum_range_rect_eq_diag_add_corner, ty, value)
}

/// Declare this module's two results in order: the general split lemma
/// [`declare_sum_range_split`], then the headline
/// [`declare_sum_range_rect_eq_diag_add_corner`].
pub(super) fn declare_rectangle(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    declare_sum_range_split(d, p)?;
    declare_sum_range_rect_eq_diag_add_corner(d, p)?;
    Ok(())
}
