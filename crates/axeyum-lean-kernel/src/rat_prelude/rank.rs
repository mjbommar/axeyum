//! `Rat.rank` — the rank of a matrix over `ℚ`, read off the row-echelon form
//! [`super::echelon`] builds (ADR-1555).
//!
//! ## What rank is here
//!
//! `rank A rows cols` is the number of rows of `rowEchelon A rows cols` that
//! are **nonzero**, and "nonzero" is decided by
//! `Rat.leadingIndex`: a zero row's leading index is `cols` (that
//! convention is `echelon.rs`'s, and it is load-bearing exactly here), so a
//! row is nonzero precisely when its leading index is strictly below `cols`.
//! `Rat.nonzeroRowB` is that test as a `Bool`, and `rank` is a
//! plain `Nat.countRange` of it over the row
//! index.
//!
//! Everything is **computed**: `rank` is a `Definition` the kernel reduces, so
//! `rank [[1,2],[3,4]] 2 2` evaluates to `2` and a wrong definition is
//! observable. The trusted gate cannot see a wrong `Definition` — `rank` has
//! type `Mat → Nat → Nat → Nat` whatever it returns — so `rank_tests.rs`
//! reduces it at concrete matrices whose rank was worked out by hand.
//!
//! ## The count is NOT capped at `cols`, deliberately
//!
//! `min (countRange …) cols` would make `rank_le_cols` free.
//! It would also make a *broken* elimination unobservable: an elimination that
//! produced four nonzero rows in three columns would be silently reported as
//! `3` instead of as `4`, and the evaluation tests below could not tell the
//! difference. A bound that holds because the definition truncates is not a
//! theorem about rank, so the cap is not taken and `rank_le_cols` is left
//! open — see the module note below and ADR-1555.
//!
//! ## What is provable here, and what is not
//!
//! - `Rat.rank_le_rows` is immediate from `Nat.countRange_le`: the
//!   count of a predicate over `[0, rows)` is at most `rows`, whatever the
//!   predicate is. No property of `rowEchelon` is needed.
//! - `rank ≤ cols` is **not** provable from anything in this module or in
//!   `echelon.rs`. It says the echelon form has at most one pivot per column,
//!   which is the strictly-increasing-leading-index property — i.e. exactly
//!   `rowEchelon_isEchelon`, obligation 4 of ADR-1554, which was deliberately
//!   not attempted. ADR-1555 sizes the residue.
//! - Rank INVARIANCE under the three elementary row operations is likewise not
//!   provable from `echelon.rs`'s three inverse laws. Two independent reasons,
//!   either of which is fatal on its own, are recorded in ADR-1555; the short
//!   version is that this kernel has no `funext`, so a POINTWISE law like
//!   `rowSwap_involutive` cannot be transported under `rank` at all — `rank`
//!   takes the matrix as an argument, and two pointwise-equal matrices are not
//!   `Eq` here. `rank_tests.rs` therefore checks invariance where it IS
//!   checkable: by reduction, at concrete matrices.

use super::RatPrelude;
use super::matrix_det::mat_ty;
use crate::KernelError;
use crate::env::{Declaration, ReducibilityHint};
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::NatOps;

/// Delta height for `Rat.nonzeroRowB`, one above
/// `Rat.leadingIndex`'s 58.
const NONZERO_ROW_HEIGHT: u16 = 59;

/// Delta height for [`RatPrelude::rank`], one above `Rat.rowEchelon`'s 61 so
/// the count unfolds before the elimination underneath it.
const RANK_HEIGHT: u16 = 62;

/// Declare everything this file builds.
///
/// # Errors
///
/// Returns the trusted gate's rejection — an `Err` means the kernel
/// **refused** a declaration, not that a script gave up.
pub(super) fn declare_rank(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    declare_nonzero_row_b(d, p)?;
    declare_nonzero_row_b_eq_ble(d, p)?;
    declare_nonzero_row_b_zero_cols(d, p)?;
    declare_rank_definition(d, p)?;
    declare_rank_eq_count_range(d, p)?;
    declare_rank_le_rows(d, p)?;
    declare_rank_zero_rows(d, p)?;
    declare_count_range_nonzero_row_b_zero(d, p)?;
    declare_rank_zero_cols(d, p)?;
    Ok(())
}

// --- small shapes ----------------------------------------------------------

/// `Rat.nonzeroRowB E cols r`.
pub(super) fn rnonzero_row_b(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    e: ExprId,
    cols: ExprId,
    r: ExprId,
) -> ExprId {
    d.const_app(p.nonzero_row_b, &[e, cols, r])
}

/// `Rat.nonzeroRowB E cols`, the `Nat → Bool` predicate `Nat.countRange`
/// consumes.
fn nonzero_row_pred(d: &mut IntDev<'_>, p: RatPrelude, e: ExprId, cols: ExprId) -> ExprId {
    d.const_app(p.nonzero_row_b, &[e, cols])
}

/// `Nat.countRange f n`.
fn count_range(d: &mut IntDev<'_>, f: ExprId, n: ExprId) -> ExprId {
    let name = d.prelude().count_range;
    d.const_app(name, &[f, n])
}

/// `Rat.rank M rows cols`.
pub(super) fn rrank(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    m: ExprId,
    rows: ExprId,
    cols: ExprId,
) -> ExprId {
    d.const_app(p.rank, &[m, rows, cols])
}

/// `Rat.rowEchelon M rows cols`.
fn row_echelon(d: &mut IntDev<'_>, p: RatPrelude, m: ExprId, rows: ExprId, cols: ExprId) -> ExprId {
    d.const_app(p.row_echelon, &[m, rows, cols])
}

// --- the nonzero-row test --------------------------------------------------

/// Admit `Rat.nonzeroRowB : Mat -> Nat -> Nat -> Bool`,
/// `nonzeroRowB E cols r := Nat.ble (succ (leadingIndex E r cols)) cols`.
///
/// The matrix comes first and the row index LAST so that `nonzeroRowB E cols`
/// is already the `Nat → Bool` predicate `Nat.countRange` wants; a signature
/// with `r` in the middle would need a lambda at every use site, and a lambda
/// is what `Nat.countRange_congr` cannot see through.
fn declare_nonzero_row_b(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let bool_ty = d.bool_ty();
    let mty = mat_ty(d);

    let e_fv = d.fresh_fvar();
    let e = d.kernel().fvar(e_fv);
    let cols_fv = d.fresh_fvar();
    let cols = d.kernel().fvar(cols_fv);
    let r_fv = d.fresh_fvar();
    let r = d.kernel().fvar(r_fv);

    let lead = d.const_app(p.leading_index, &[e, r, cols]);
    let slead = d.succ(lead);
    let body = NatOps::ble(d, slead, cols);

    let value = {
        let over_r = d.lam_fv(r_fv, nat, body);
        let over_cols = d.lam_fv(cols_fv, nat, over_r);
        d.lam_fv(e_fv, mty, over_cols)
    };
    let ty = {
        let over_r = d.arrow(nat, bool_ty);
        let over_cols = d.arrow(nat, over_r);
        d.arrow(mty, over_cols)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.nonzero_row_b,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(NONZERO_ROW_HEIGHT),
    })
}

/// Admit `Rat.nonzeroRowB_eq_ble : ∀ E cols r,
/// nonzeroRowB E cols r = Nat.ble (succ (leadingIndex E r cols)) cols`.
///
/// The defining equation, by `Eq.refl`. It exists because every future proof
/// about `rank` has to get from the predicate to the leading index, and
/// unfolding a `Definition` by hand inside a proof term is exactly the
/// full-unfold cost `CLAUDE.md` warns about.
fn declare_nonzero_row_b_eq_ble(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let mty = mat_ty(d);

    let e_fv = d.fresh_fvar();
    let e = d.kernel().fvar(e_fv);
    let cols_fv = d.fresh_fvar();
    let cols = d.kernel().fvar(cols_fv);
    let r_fv = d.fresh_fvar();
    let r = d.kernel().fvar(r_fv);

    let lhs = rnonzero_row_b(d, p, e, cols, r);
    let lead = d.const_app(p.leading_index, &[e, r, cols]);
    let slead = d.succ(lead);
    let rhs = NatOps::ble(d, slead, cols);
    let stmt = d.bool_eq(lhs, rhs);
    let proof = d.bool_refl(rhs);

    let ty = {
        let over_r = d.pi_fv(r_fv, nat, stmt);
        let over_cols = d.pi_fv(cols_fv, nat, over_r);
        d.pi_fv(e_fv, mty, over_cols)
    };
    let value = {
        let over_r = d.lam_fv(r_fv, nat, proof);
        let over_cols = d.lam_fv(cols_fv, nat, over_r);
        d.lam_fv(e_fv, mty, over_cols)
    };
    d.declare_theorem(p.nonzero_row_b_eq_ble, ty, value)
}

/// Admit `Rat.nonzeroRowB_zero_cols : ∀ E r, nonzeroRowB E 0 r = false`.
///
/// With no columns every row is zero, and this holds by ι-reduction alone:
/// `Nat.ble (succ _) zero` steps to `false` without ever evaluating the
/// leading index, so the equation is `Eq.refl` at a SYMBOLIC matrix and a
/// symbolic row. That is what makes [`declare_rank_zero_cols`] cheap.
fn declare_nonzero_row_b_zero_cols(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let mty = mat_ty(d);

    let e_fv = d.fresh_fvar();
    let e = d.kernel().fvar(e_fv);
    let r_fv = d.fresh_fvar();
    let r = d.kernel().fvar(r_fv);

    let zero_n = d.zero();
    let lhs = rnonzero_row_b(d, p, e, zero_n, r);
    let false_v = d.bool_false();
    let stmt = d.bool_eq(lhs, false_v);
    let proof = d.bool_refl(false_v);

    let ty = {
        let over_r = d.pi_fv(r_fv, nat, stmt);
        d.pi_fv(e_fv, mty, over_r)
    };
    let value = {
        let over_r = d.lam_fv(r_fv, nat, proof);
        d.lam_fv(e_fv, mty, over_r)
    };
    d.declare_theorem(p.nonzero_row_b_zero_cols, ty, value)
}

// --- rank ------------------------------------------------------------------

/// Admit `Rat.rank : Mat -> Nat -> Nat -> Nat`,
/// `rank M rows cols := Nat.countRange (nonzeroRowB (rowEchelon M rows cols) cols) rows`.
fn declare_rank_definition(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let mty = mat_ty(d);

    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let rows_fv = d.fresh_fvar();
    let rows = d.kernel().fvar(rows_fv);
    let cols_fv = d.fresh_fvar();
    let cols = d.kernel().fvar(cols_fv);

    let echelon = row_echelon(d, p, m, rows, cols);
    let pred = nonzero_row_pred(d, p, echelon, cols);
    let body = count_range(d, pred, rows);

    let value = {
        let over_cols = d.lam_fv(cols_fv, nat, body);
        let over_rows = d.lam_fv(rows_fv, nat, over_cols);
        d.lam_fv(m_fv, mty, over_rows)
    };
    let ty = {
        let over_cols = d.arrow(nat, nat);
        let over_rows = d.arrow(nat, over_cols);
        d.arrow(mty, over_rows)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.rank,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(RANK_HEIGHT),
    })
}

/// Admit `Rat.rank_eq_countRange : ∀ M rows cols, rank M rows cols =
/// Nat.countRange (nonzeroRowB (rowEchelon M rows cols) cols) rows`.
///
/// `Eq.refl`. Every `Nat.countRange` law — `countRange_le`, `countRange_congr`,
/// `countRange_split` — reaches `rank` through this equation and nothing else.
fn declare_rank_eq_count_range(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let mty = mat_ty(d);

    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let rows_fv = d.fresh_fvar();
    let rows = d.kernel().fvar(rows_fv);
    let cols_fv = d.fresh_fvar();
    let cols = d.kernel().fvar(cols_fv);

    let lhs = rrank(d, p, m, rows, cols);
    let echelon = row_echelon(d, p, m, rows, cols);
    let pred = nonzero_row_pred(d, p, echelon, cols);
    let rhs = count_range(d, pred, rows);
    let stmt = d.eq(lhs, rhs);
    let proof = d.refl(rhs);

    let ty = {
        let over_cols = d.pi_fv(cols_fv, nat, stmt);
        let over_rows = d.pi_fv(rows_fv, nat, over_cols);
        d.pi_fv(m_fv, mty, over_rows)
    };
    let value = {
        let over_cols = d.lam_fv(cols_fv, nat, proof);
        let over_rows = d.lam_fv(rows_fv, nat, over_cols);
        d.lam_fv(m_fv, mty, over_rows)
    };
    d.declare_theorem(p.rank_eq_count_range, ty, value)
}

/// Admit `Rat.rank_le_rows : ∀ M rows cols, Le (rank M rows cols) rows`.
///
/// One application of `Nat.countRange_le`. Note what is NOT used: no property
/// of `rowEchelon`, of `leadingIndex`, or of the row operations. The bound
/// holds because a count over `[0, rows)` cannot exceed `rows` whatever the
/// predicate does, which is why this side of the dimension bound is free and
/// `rank ≤ cols` is not.
fn declare_rank_le_rows(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let mty = mat_ty(d);

    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let rows_fv = d.fresh_fvar();
    let rows = d.kernel().fvar(rows_fv);
    let cols_fv = d.fresh_fvar();
    let cols = d.kernel().fvar(cols_fv);

    let lhs = rrank(d, p, m, rows, cols);
    let stmt = NatOps::le(d, lhs, rows);

    let echelon = row_echelon(d, p, m, rows, cols);
    let pred = nonzero_row_pred(d, p, echelon, cols);
    let count_range_le = d.prelude().count_range_le;
    let proof = d.lemma(count_range_le, &[pred, rows]);

    let ty = {
        let over_cols = d.pi_fv(cols_fv, nat, stmt);
        let over_rows = d.pi_fv(rows_fv, nat, over_cols);
        d.pi_fv(m_fv, mty, over_rows)
    };
    let value = {
        let over_cols = d.lam_fv(cols_fv, nat, proof);
        let over_rows = d.lam_fv(rows_fv, nat, over_cols);
        d.lam_fv(m_fv, mty, over_rows)
    };
    d.declare_theorem(p.rank_le_rows, ty, value)
}

/// Admit `Rat.rank_zero_rows : ∀ M cols, rank M 0 cols = 0`.
///
/// `Eq.refl`: `Nat.countRange f 0` ι-reduces to `0` without touching `f`, so
/// the elimination is never run. The degenerate control for
/// [`declare_rank_le_rows`] — at `rows = 0` the bound is an equality.
fn declare_rank_zero_rows(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let mty = mat_ty(d);

    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let cols_fv = d.fresh_fvar();
    let cols = d.kernel().fvar(cols_fv);

    let zero_n = d.zero();
    let lhs = rrank(d, p, m, zero_n, cols);
    let zero_r = d.zero();
    let stmt = d.eq(lhs, zero_r);
    let proof = d.refl(zero_r);

    let ty = {
        let over_cols = d.pi_fv(cols_fv, nat, stmt);
        d.pi_fv(m_fv, mty, over_cols)
    };
    let value = {
        let over_cols = d.lam_fv(cols_fv, nat, proof);
        d.lam_fv(m_fv, mty, over_cols)
    };
    d.declare_theorem(p.rank_zero_rows, ty, value)
}

/// Admit `Rat.countRange_nonzeroRowB_zero : ∀ E n,
/// Nat.countRange (nonzeroRowB E 0) n = 0`.
///
/// Induction on `n` with the matrix `E` held FIXED, which is the whole reason
/// this is a separate lemma: in `rank M rows 0` the matrix is
/// `rowEchelon M rows 0`, so it depends on the row count and an induction on
/// `rows` done in place would face a different predicate in the step than the
/// one the induction hypothesis is about. Generalising `E` first is the
/// standard fix and it makes both cases `Eq.refl`-shaped: the successor step's
/// increment is `bool_select_nat false 1 0`, i.e. `0`, and `Nat.add` recurses
/// on its right argument, so `countRange f (succ n)` is definitionally
/// `countRange f n` here and the induction hypothesis IS the goal.
fn declare_count_range_nonzero_row_b_zero(
    d: &mut IntDev<'_>,
    p: RatPrelude,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let mty = mat_ty(d);

    let e_fv = d.fresh_fvar();
    let e = d.kernel().fvar(e_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let zero_cols = d.zero();
    let pred = nonzero_row_pred(d, p, e, zero_cols);

    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let cr = count_range(d, pred, x);
        let zero_r = d.zero();
        d.eq(cr, zero_r)
    };
    let stmt = motive(d, n);
    let proof = d.induct(
        &motive,
        &|d| {
            let zero_r = d.zero();
            d.refl(zero_r)
        },
        &|_d, _j, ih| ih,
        n,
    );

    let ty = {
        let over_n = d.pi_fv(n_fv, nat, stmt);
        d.pi_fv(e_fv, mty, over_n)
    };
    let value = {
        let over_n = d.lam_fv(n_fv, nat, proof);
        d.lam_fv(e_fv, mty, over_n)
    };
    d.declare_theorem(p.count_range_nonzero_row_b_zero, ty, value)
}

/// Admit `Rat.rank_zero_cols : ∀ M rows, rank M rows 0 = 0`.
///
/// [`declare_count_range_nonzero_row_b_zero`] instantiated at the echelon form
/// itself. The second degenerate control: `rank ≤ cols` is unproven in
/// general, but at `cols = 0` it holds, and it holds as an EQUALITY — so a
/// definition that counted rows regardless of the leading index would fail
/// here even though it satisfies `rank_le_rows`.
fn declare_rank_zero_cols(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let mty = mat_ty(d);

    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let rows_fv = d.fresh_fvar();
    let rows = d.kernel().fvar(rows_fv);

    let zero_cols = d.zero();
    let lhs = rrank(d, p, m, rows, zero_cols);
    let zero_r = d.zero();
    let stmt = d.eq(lhs, zero_r);

    let echelon = row_echelon(d, p, m, rows, zero_cols);
    let proof = d.lemma(p.count_range_nonzero_row_b_zero, &[echelon, rows]);

    let ty = {
        let over_rows = d.pi_fv(rows_fv, nat, stmt);
        d.pi_fv(m_fv, mty, over_rows)
    };
    let value = {
        let over_rows = d.lam_fv(rows_fv, nat, proof);
        d.lam_fv(m_fv, mty, over_rows)
    };
    d.declare_theorem(p.rank_zero_cols, ty, value)
}
