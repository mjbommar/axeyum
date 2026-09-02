//! `Rat.rankCols` and `Rat.nullity` — rank-nullity over `ℚ` in **column form**
//! (ADR-1558).
//!
//! ## Why columns, and why that makes the theorem free
//!
//! The obvious definition is `nullity := cols - rank`. It is also the expensive
//! one: it makes `rankCols + nullity = cols` depend on `rank ≤ cols`, which
//! asserts that the echelon form has at most one pivot per column — i.e.
//! `rowEchelon_isEchelon`, ADR-1554 obligation 4, which nobody has proved.
//! `rank_le_cols` is open in this tree for exactly that reason (ADR-1555).
//!
//! So this module does not subtract. It **counts the other side**:
//!
//! ```text
//! isPivotColB E rows cols j := some r < rows has leadingIndex E r cols = j
//! rankCols M rows cols      := countRange (isPivotColB (rowEchelon M rows cols) rows cols) cols
//! nullity  M rows cols      := countRange (setCompl (isPivotColB …)) cols
//! ```
//!
//! and then `rankCols M rows cols + nullity M rows cols = cols` is
//! `Nat.countRange_compl` — *"a predicate and its complement partition
//! `[0, n)`"* — instantiated at one predicate. It is a fact about counting,
//! not about elimination: nothing in `Rat.rank_nullity`'s proof knows that
//! `rowEchelon` computes an echelon form, or even that it is not the identity.
//! That is the point. The obligation does not disappear; it is **relocated**,
//! entirely, into one bridge.
//!
//! ## The bridge, and what it costs
//!
//! `rank M rows cols = rankCols M rows cols` — the number of nonzero ROWS of
//! the echelon form equals the number of pivot COLUMNS — is where
//! `rowEchelon_isEchelon` is genuinely required, and it did NOT land here.
//! ADR-1558 sizes it and records the term that gets stuck. What is checkable
//! without it is the bridge at concrete matrices, which
//! [`super::nullity_tests`] does at all six.
//!
//! Note what this buys even with the bridge open: `rankCols ≤ cols` is FREE
//! ([`declare_rank_cols_le_cols`], one `Nat.countRange_le`), where the row-form
//! `rank ≤ cols` is not. A count over the columns cannot exceed the number of
//! columns whatever the predicate does. The two statements are only the same
//! statement once the bridge is proved — and that asymmetry is the honest
//! summary of what the column form is worth.
//!
//! ## Everything is computed
//!
//! `isPivotColB`, `rankCols` and `nullity` are `Definition`s the kernel
//! reduces, so `nullity [[1,2],[2,4]] 2 2` evaluates to `1` and a wrong
//! definition is observable. The trusted gate cannot see a wrong `Definition`
//! — `nullity` has type `Mat → Nat → Nat → Nat` whatever it returns — so
//! `nullity_tests.rs` reduces each at concrete matrices whose pivot columns
//! were worked out by hand, each against a control that must FAIL.

use super::RatPrelude;
use super::echelon::{bool_select_at, nat_fuel_rec};
use super::matrix_det::mat_ty;
use crate::KernelError;
use crate::env::{Declaration, ReducibilityHint};
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::NatOps;

/// Delta height for `Rat.pivotColSearchAux`, one above
/// `Rat.leadingIndex`'s 58 so the leading index unfolds underneath the scan.
const PIVOT_COL_AUX_HEIGHT: u16 = 59;

/// Delta height for `Rat.isPivotColB`, one above the scan it wraps.
const IS_PIVOT_COL_HEIGHT: u16 = 60;

/// Delta height for `Rat.rankCols` and `Rat.nullity`, one above
/// `Rat.rowEchelon`'s 61 — the same height `Rat.rank` carries, and for the
/// same reason: the count must unfold before the elimination underneath it.
const RANK_COLS_HEIGHT: u16 = 62;

/// Declare everything this file builds.
///
/// # Errors
///
/// Returns the trusted gate's rejection — an `Err` means the kernel
/// **refused** a declaration, not that a script gave up.
pub(super) fn declare_nullity(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    declare_pivot_col_search_aux(d, p)?;
    declare_is_pivot_col_b(d, p)?;
    declare_is_pivot_col_b_eq_search(d, p)?;
    declare_is_pivot_col_b_zero_rows(d, p)?;
    declare_rank_cols_definition(d, p)?;
    declare_rank_cols_eq_count_range(d, p)?;
    declare_nullity_definition(d, p)?;
    declare_nullity_eq_count_range(d, p)?;
    declare_rank_nullity(d, p)?;
    declare_rank_cols_le_cols(d, p)?;
    declare_nullity_le_cols(d, p)?;
    declare_rank_cols_zero_cols(d, p)?;
    declare_nullity_zero_cols(d, p)?;
    declare_count_range_is_pivot_col_b_zero_rows(d, p)?;
    declare_rank_cols_zero_rows(d, p)?;
    declare_nullity_zero_rows(d, p)?;
    Ok(())
}

// --- small shapes ----------------------------------------------------------

/// `Rat.isPivotColB E rows cols j`.
pub(super) fn ris_pivot_col_b(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    e: ExprId,
    rows: ExprId,
    cols: ExprId,
    j: ExprId,
) -> ExprId {
    d.const_app(p.is_pivot_col_b, &[e, rows, cols, j])
}

/// `Rat.isPivotColB E rows cols`, the `Nat → Bool` predicate `Nat.countRange`
/// consumes.
fn pivot_col_pred(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    e: ExprId,
    rows: ExprId,
    cols: ExprId,
) -> ExprId {
    d.const_app(p.is_pivot_col_b, &[e, rows, cols])
}

/// `Nat.setCompl f`.
fn set_compl(d: &mut IntDev<'_>, f: ExprId) -> ExprId {
    let name = d.prelude().set_compl;
    d.const_app(name, &[f])
}

/// `Nat.countRange f n`.
fn count_range(d: &mut IntDev<'_>, f: ExprId, n: ExprId) -> ExprId {
    let name = d.prelude().count_range;
    d.const_app(name, &[f, n])
}

/// `Rat.rankCols M rows cols`.
pub(super) fn rrank_cols(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    m: ExprId,
    rows: ExprId,
    cols: ExprId,
) -> ExprId {
    d.const_app(p.rank_cols, &[m, rows, cols])
}

/// `Rat.nullity M rows cols`.
pub(super) fn rnullity(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    m: ExprId,
    rows: ExprId,
    cols: ExprId,
) -> ExprId {
    d.const_app(p.nullity, &[m, rows, cols])
}

/// `Rat.rowEchelon M rows cols`.
fn row_echelon(d: &mut IntDev<'_>, p: RatPrelude, m: ExprId, rows: ExprId, cols: ExprId) -> ExprId {
    d.const_app(p.row_echelon, &[m, rows, cols])
}

// --- the pivot-column test -------------------------------------------------

/// Admit `Rat.pivotColSearchAux : Mat -> Nat -> Nat -> Nat -> Nat -> Nat -> Bool`,
/// `pivotColSearchAux E rows cols j fuel r`.
///
/// `true` when some `r' >= r` below `rows` has `leadingIndex E r' cols = j`,
/// and `false` when the fuel runs out or the scan reaches `rows`. Both
/// exhaustion answers are `false` on purpose, exactly as
/// `Rat.pivotSearchAux` returns `rows` for both of its: a caller reads "no such
/// row" from one test and never has to distinguish "searched everything" from
/// "gave up".
///
/// `E`, `rows`, `cols` and `j` are fixed and sit OUTSIDE the recursion; only
/// the row index travels inside it.
fn declare_pivot_col_search_aux(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let bool_ty = d.bool_ty();
    let mty = mat_ty(d);

    let e_fv = d.fresh_fvar();
    let e = d.kernel().fvar(e_fv);
    let rows_fv = d.fresh_fvar();
    let rows = d.kernel().fvar(rows_fv);
    let cols_fv = d.fresh_fvar();
    let cols = d.kernel().fvar(cols_fv);
    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);

    let inner_ty = d.arrow(nat, bool_ty);

    let zero_case = {
        let r_fv = d.fresh_fvar();
        let false_v = d.bool_false();
        d.lam_fv(r_fv, nat, false_v)
    };
    let succ_case = {
        let n_fv = d.fresh_fvar();
        let ih_fv = d.fresh_fvar();
        let ih = d.kernel().fvar(ih_fv);
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);

        let lead = d.const_app(p.leading_index, &[e, r, cols]);
        let hit = NatOps::beq(d, lead, j);
        let sr = d.succ(r);
        let recurse = d.apply(ih, &[sr]);
        let true_v = d.bool_true();
        let keep_looking = bool_select_at(d, bool_ty, hit, true_v, recurse);
        let out_of_range = NatOps::ble(d, rows, r);
        let false_v = d.bool_false();
        let body = bool_select_at(d, bool_ty, out_of_range, false_v, keep_looking);

        let over_r = d.lam_fv(r_fv, nat, body);
        let over_ih = d.lam_fv(ih_fv, inner_ty, over_r);
        d.lam_fv(n_fv, nat, over_ih)
    };

    let fuel_fv = d.fresh_fvar();
    let fuel = d.kernel().fvar(fuel_fv);
    let rec_app = nat_fuel_rec(d, inner_ty, zero_case, succ_case, fuel);
    let r_outer_fv = d.fresh_fvar();
    let r_outer = d.kernel().fvar(r_outer_fv);
    let applied = d.apply(rec_app, &[r_outer]);

    let value = {
        let over_r = d.lam_fv(r_outer_fv, nat, applied);
        let over_fuel = d.lam_fv(fuel_fv, nat, over_r);
        let over_j = d.lam_fv(j_fv, nat, over_fuel);
        let over_cols = d.lam_fv(cols_fv, nat, over_j);
        let over_rows = d.lam_fv(rows_fv, nat, over_cols);
        d.lam_fv(e_fv, mty, over_rows)
    };
    let ty = {
        let over_r = d.arrow(nat, bool_ty);
        let over_fuel = d.arrow(nat, over_r);
        let over_j = d.arrow(nat, over_fuel);
        let over_cols = d.arrow(nat, over_j);
        let over_rows = d.arrow(nat, over_cols);
        d.arrow(mty, over_rows)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.pivot_col_search_aux,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(PIVOT_COL_AUX_HEIGHT),
    })
}

/// Admit `Rat.isPivotColB : Mat -> Nat -> Nat -> Nat -> Bool`,
/// `isPivotColB E rows cols j := pivotColSearchAux E rows cols j rows 0`.
///
/// Fuel `rows` is sufficient because the scan starts at `0` and stops at
/// `rows`. The column index comes LAST so that `isPivotColB E rows cols` is
/// already the `Nat → Bool` predicate `Nat.countRange` wants — the same
/// argument-order discipline `Rat.nonzeroRowB` follows, and for the same
/// reason: a lambda at the use site is what `Nat.countRange_congr` cannot see
/// through.
fn declare_is_pivot_col_b(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let bool_ty = d.bool_ty();
    let mty = mat_ty(d);

    let e_fv = d.fresh_fvar();
    let e = d.kernel().fvar(e_fv);
    let rows_fv = d.fresh_fvar();
    let rows = d.kernel().fvar(rows_fv);
    let cols_fv = d.fresh_fvar();
    let cols = d.kernel().fvar(cols_fv);
    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);

    let zero_n = d.zero();
    let body = d.const_app(p.pivot_col_search_aux, &[e, rows, cols, j, rows, zero_n]);

    let value = {
        let over_j = d.lam_fv(j_fv, nat, body);
        let over_cols = d.lam_fv(cols_fv, nat, over_j);
        let over_rows = d.lam_fv(rows_fv, nat, over_cols);
        d.lam_fv(e_fv, mty, over_rows)
    };
    let ty = {
        let over_j = d.arrow(nat, bool_ty);
        let over_cols = d.arrow(nat, over_j);
        let over_rows = d.arrow(nat, over_cols);
        d.arrow(mty, over_rows)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.is_pivot_col_b,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(IS_PIVOT_COL_HEIGHT),
    })
}

/// Admit `Rat.isPivotColB_eq_search : ∀ E rows cols j,
/// isPivotColB E rows cols j = pivotColSearchAux E rows cols j rows 0`.
///
/// The defining equation, by `Eq.refl`. It exists so a future proof about
/// `rankCols` can reach the scan without unfolding a `Definition` by hand
/// inside a proof term — the full-unfold cost `CLAUDE.md` warns about.
fn declare_is_pivot_col_b_eq_search(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let mty = mat_ty(d);

    let e_fv = d.fresh_fvar();
    let e = d.kernel().fvar(e_fv);
    let rows_fv = d.fresh_fvar();
    let rows = d.kernel().fvar(rows_fv);
    let cols_fv = d.fresh_fvar();
    let cols = d.kernel().fvar(cols_fv);
    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);

    let lhs = ris_pivot_col_b(d, p, e, rows, cols, j);
    let zero_n = d.zero();
    let rhs = d.const_app(p.pivot_col_search_aux, &[e, rows, cols, j, rows, zero_n]);
    let stmt = d.bool_eq(lhs, rhs);
    let proof = d.bool_refl(rhs);

    let ty = {
        let over_j = d.pi_fv(j_fv, nat, stmt);
        let over_cols = d.pi_fv(cols_fv, nat, over_j);
        let over_rows = d.pi_fv(rows_fv, nat, over_cols);
        d.pi_fv(e_fv, mty, over_rows)
    };
    let value = {
        let over_j = d.lam_fv(j_fv, nat, proof);
        let over_cols = d.lam_fv(cols_fv, nat, over_j);
        let over_rows = d.lam_fv(rows_fv, nat, over_cols);
        d.lam_fv(e_fv, mty, over_rows)
    };
    d.declare_theorem(p.is_pivot_col_b_eq_search, ty, value)
}

/// Admit `Rat.isPivotColB_zero_rows : ∀ E cols j, isPivotColB E 0 cols j = false`.
///
/// With no rows there is no pivot anywhere, and this holds by ι-reduction
/// alone: the fuel is `rows = 0`, so `Nat.rec` takes its zero branch and the
/// leading index is never evaluated. `Eq.refl` at a SYMBOLIC matrix, a
/// symbolic column count and a symbolic column — which is what makes
/// [`declare_count_range_is_pivot_col_b_zero_rows`] an induction whose step is
/// literally the induction hypothesis.
fn declare_is_pivot_col_b_zero_rows(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let mty = mat_ty(d);

    let e_fv = d.fresh_fvar();
    let e = d.kernel().fvar(e_fv);
    let cols_fv = d.fresh_fvar();
    let cols = d.kernel().fvar(cols_fv);
    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);

    let zero_rows = d.zero();
    let lhs = ris_pivot_col_b(d, p, e, zero_rows, cols, j);
    let false_v = d.bool_false();
    let stmt = d.bool_eq(lhs, false_v);
    let proof = d.bool_refl(false_v);

    let ty = {
        let over_j = d.pi_fv(j_fv, nat, stmt);
        let over_cols = d.pi_fv(cols_fv, nat, over_j);
        d.pi_fv(e_fv, mty, over_cols)
    };
    let value = {
        let over_j = d.lam_fv(j_fv, nat, proof);
        let over_cols = d.lam_fv(cols_fv, nat, over_j);
        d.lam_fv(e_fv, mty, over_cols)
    };
    d.declare_theorem(p.is_pivot_col_b_zero_rows, ty, value)
}

// --- rankCols and nullity --------------------------------------------------

/// Admit `Rat.rankCols : Mat -> Nat -> Nat -> Nat`, `rankCols M rows cols :=
/// Nat.countRange (isPivotColB (rowEchelon M rows cols) rows cols) cols`.
fn declare_rank_cols_definition(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let mty = mat_ty(d);

    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let rows_fv = d.fresh_fvar();
    let rows = d.kernel().fvar(rows_fv);
    let cols_fv = d.fresh_fvar();
    let cols = d.kernel().fvar(cols_fv);

    let echelon = row_echelon(d, p, m, rows, cols);
    let pred = pivot_col_pred(d, p, echelon, rows, cols);
    let body = count_range(d, pred, cols);

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
        name: p.rank_cols,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(RANK_COLS_HEIGHT),
    })
}

/// Admit `Rat.rankCols_eq_countRange : ∀ M rows cols, rankCols M rows cols =
/// Nat.countRange (isPivotColB (rowEchelon M rows cols) rows cols) cols`.
///
/// `Eq.refl`, and the route every `Nat.countRange` law takes to `rankCols` —
/// the twin of `Rat.rank_eq_countRange`.
fn declare_rank_cols_eq_count_range(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let mty = mat_ty(d);

    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let rows_fv = d.fresh_fvar();
    let rows = d.kernel().fvar(rows_fv);
    let cols_fv = d.fresh_fvar();
    let cols = d.kernel().fvar(cols_fv);

    let lhs = rrank_cols(d, p, m, rows, cols);
    let echelon = row_echelon(d, p, m, rows, cols);
    let pred = pivot_col_pred(d, p, echelon, rows, cols);
    let rhs = count_range(d, pred, cols);
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
    d.declare_theorem(p.rank_cols_eq_count_range, ty, value)
}

/// Admit `Rat.nullity : Mat -> Nat -> Nat -> Nat`, `nullity M rows cols :=
/// Nat.countRange (Nat.setCompl (isPivotColB (rowEchelon M rows cols) rows cols)) cols`.
///
/// The **free** columns: those that are not pivot columns. Stated with
/// `Nat.setCompl` and not with an inline `fun j => if … then false else true`
/// precisely so that [`declare_rank_nullity`] is one application of
/// `Nat.countRange_compl` and not a re-proof of it.
fn declare_nullity_definition(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let mty = mat_ty(d);

    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let rows_fv = d.fresh_fvar();
    let rows = d.kernel().fvar(rows_fv);
    let cols_fv = d.fresh_fvar();
    let cols = d.kernel().fvar(cols_fv);

    let echelon = row_echelon(d, p, m, rows, cols);
    let pred = pivot_col_pred(d, p, echelon, rows, cols);
    let compl = set_compl(d, pred);
    let body = count_range(d, compl, cols);

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
        name: p.nullity,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(RANK_COLS_HEIGHT),
    })
}

/// Admit `Rat.nullity_eq_countRange : ∀ M rows cols, nullity M rows cols =
/// Nat.countRange (Nat.setCompl (isPivotColB (rowEchelon M rows cols) rows cols)) cols`.
///
/// `Eq.refl`.
fn declare_nullity_eq_count_range(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let mty = mat_ty(d);

    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let rows_fv = d.fresh_fvar();
    let rows = d.kernel().fvar(rows_fv);
    let cols_fv = d.fresh_fvar();
    let cols = d.kernel().fvar(cols_fv);

    let lhs = rnullity(d, p, m, rows, cols);
    let echelon = row_echelon(d, p, m, rows, cols);
    let pred = pivot_col_pred(d, p, echelon, rows, cols);
    let compl = set_compl(d, pred);
    let rhs = count_range(d, compl, cols);
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
    d.declare_theorem(p.nullity_eq_count_range, ty, value)
}

// --- the headline ----------------------------------------------------------

/// Admit `Rat.rank_nullity : ∀ M rows cols,
/// Nat.add (rankCols M rows cols) (nullity M rows cols) = cols`.
///
/// **One application of `Nat.countRange_compl`**, at the predicate
/// `isPivotColB (rowEchelon M rows cols) rows cols`. Symbolic in all three
/// arguments: the matrix is never evaluated, `rowEchelon` is never run, and no
/// property of it is used or needed. That is exactly the point of the column
/// form — see this module's note.
fn declare_rank_nullity(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let mty = mat_ty(d);

    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let rows_fv = d.fresh_fvar();
    let rows = d.kernel().fvar(rows_fv);
    let cols_fv = d.fresh_fvar();
    let cols = d.kernel().fvar(cols_fv);

    let rc = rrank_cols(d, p, m, rows, cols);
    let nl = rnullity(d, p, m, rows, cols);
    let sum = d.add(rc, nl);
    let stmt = d.eq(sum, cols);

    let echelon = row_echelon(d, p, m, rows, cols);
    let pred = pivot_col_pred(d, p, echelon, rows, cols);
    let count_range_compl = d.prelude().count_range_compl;
    let proof = d.lemma(count_range_compl, &[pred, cols]);

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
    d.declare_theorem(p.rank_nullity, ty, value)
}

// --- the dimension bounds, both free ---------------------------------------

/// Admit `Rat.rankCols_le_cols : ∀ M rows cols, Le (rankCols M rows cols) cols`.
///
/// One `Nat.countRange_le`. Contrast `Rat.rank_le_cols`, which is OPEN: the
/// row-form count runs over `[0, rows)`, so bounding it by `cols` is a claim
/// about the echelon form, whereas the column-form count runs over
/// `[0, cols)` and the bound holds whatever the predicate does. The
/// asymmetry is the column form's whole payoff while the bridge is open.
fn declare_rank_cols_le_cols(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let mty = mat_ty(d);

    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let rows_fv = d.fresh_fvar();
    let rows = d.kernel().fvar(rows_fv);
    let cols_fv = d.fresh_fvar();
    let cols = d.kernel().fvar(cols_fv);

    let lhs = rrank_cols(d, p, m, rows, cols);
    let stmt = NatOps::le(d, lhs, cols);

    let echelon = row_echelon(d, p, m, rows, cols);
    let pred = pivot_col_pred(d, p, echelon, rows, cols);
    let count_range_le = d.prelude().count_range_le;
    let proof = d.lemma(count_range_le, &[pred, cols]);

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
    d.declare_theorem(p.rank_cols_le_cols, ty, value)
}

/// Admit `Rat.nullity_le_cols : ∀ M rows cols, Le (nullity M rows cols) cols`.
///
/// The same `Nat.countRange_le` at the complementary predicate.
fn declare_nullity_le_cols(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let mty = mat_ty(d);

    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let rows_fv = d.fresh_fvar();
    let rows = d.kernel().fvar(rows_fv);
    let cols_fv = d.fresh_fvar();
    let cols = d.kernel().fvar(cols_fv);

    let lhs = rnullity(d, p, m, rows, cols);
    let stmt = NatOps::le(d, lhs, cols);

    let echelon = row_echelon(d, p, m, rows, cols);
    let pred = pivot_col_pred(d, p, echelon, rows, cols);
    let compl = set_compl(d, pred);
    let count_range_le = d.prelude().count_range_le;
    let proof = d.lemma(count_range_le, &[compl, cols]);

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
    d.declare_theorem(p.nullity_le_cols, ty, value)
}

// --- the degenerate dimensions ---------------------------------------------

/// Admit `Rat.rankCols_zero_cols : ∀ M rows, rankCols M rows 0 = 0`.
///
/// `Eq.refl`: `Nat.countRange f 0` ι-reduces to `0` without touching `f`, so
/// the elimination is never run.
fn declare_rank_cols_zero_cols(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let mty = mat_ty(d);

    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let rows_fv = d.fresh_fvar();
    let rows = d.kernel().fvar(rows_fv);

    let zero_cols = d.zero();
    let lhs = rrank_cols(d, p, m, rows, zero_cols);
    let zero_r = d.zero();
    let stmt = d.eq(lhs, zero_r);
    let proof = d.refl(zero_r);

    let ty = {
        let over_rows = d.pi_fv(rows_fv, nat, stmt);
        d.pi_fv(m_fv, mty, over_rows)
    };
    let value = {
        let over_rows = d.lam_fv(rows_fv, nat, proof);
        d.lam_fv(m_fv, mty, over_rows)
    };
    d.declare_theorem(p.rank_cols_zero_cols, ty, value)
}

/// Admit `Rat.nullity_zero_cols : ∀ M rows, nullity M rows 0 = 0`.
///
/// `Eq.refl`, and the degenerate instance of [`declare_rank_nullity`]: at
/// `cols = 0` the partition is `0 + 0 = 0`.
fn declare_nullity_zero_cols(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let mty = mat_ty(d);

    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let rows_fv = d.fresh_fvar();
    let rows = d.kernel().fvar(rows_fv);

    let zero_cols = d.zero();
    let lhs = rnullity(d, p, m, rows, zero_cols);
    let zero_r = d.zero();
    let stmt = d.eq(lhs, zero_r);
    let proof = d.refl(zero_r);

    let ty = {
        let over_rows = d.pi_fv(rows_fv, nat, stmt);
        d.pi_fv(m_fv, mty, over_rows)
    };
    let value = {
        let over_rows = d.lam_fv(rows_fv, nat, proof);
        d.lam_fv(m_fv, mty, over_rows)
    };
    d.declare_theorem(p.nullity_zero_cols, ty, value)
}

/// Admit `Rat.countRange_isPivotColB_zeroRows : ∀ E cols n,
/// Nat.countRange (isPivotColB E 0 cols) n = 0`.
///
/// Induction on `n` with the matrix HELD FIXED, for the same reason
/// `Rat.countRange_nonzeroRowB_zero` generalises its matrix: in
/// `rankCols M 0 cols` the matrix is `rowEchelon M 0 cols`, and an induction
/// done in place would face a different predicate in the step than the one the
/// induction hypothesis is about.
///
/// Both cases are `Eq.refl`-shaped. The successor step's increment is
/// `bool_select_nat (isPivotColB E 0 cols j) 1 0`, and
/// [`declare_is_pivot_col_b_zero_rows`]'s ι-reduction makes that `0` at a
/// SYMBOLIC `j`; `Nat.add` recurses on its right argument, so
/// `countRange f (succ n)` is definitionally `countRange f n` here and the
/// induction hypothesis IS the goal.
fn declare_count_range_is_pivot_col_b_zero_rows(
    d: &mut IntDev<'_>,
    p: RatPrelude,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let mty = mat_ty(d);

    let e_fv = d.fresh_fvar();
    let e = d.kernel().fvar(e_fv);
    let cols_fv = d.fresh_fvar();
    let cols = d.kernel().fvar(cols_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let zero_rows = d.zero();
    let pred = pivot_col_pred(d, p, e, zero_rows, cols);

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
        let over_cols = d.pi_fv(cols_fv, nat, over_n);
        d.pi_fv(e_fv, mty, over_cols)
    };
    let value = {
        let over_n = d.lam_fv(n_fv, nat, proof);
        let over_cols = d.lam_fv(cols_fv, nat, over_n);
        d.lam_fv(e_fv, mty, over_cols)
    };
    d.declare_theorem(p.count_range_is_pivot_col_b_zero_rows, ty, value)
}

/// Admit `Rat.rankCols_zero_rows : ∀ M cols, rankCols M 0 cols = 0`.
///
/// [`declare_count_range_is_pivot_col_b_zero_rows`] instantiated at the
/// echelon form itself.
fn declare_rank_cols_zero_rows(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let mty = mat_ty(d);

    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let cols_fv = d.fresh_fvar();
    let cols = d.kernel().fvar(cols_fv);

    let zero_rows = d.zero();
    let lhs = rrank_cols(d, p, m, zero_rows, cols);
    let zero_r = d.zero();
    let stmt = d.eq(lhs, zero_r);

    let echelon = row_echelon(d, p, m, zero_rows, cols);
    let proof = d.lemma(
        p.count_range_is_pivot_col_b_zero_rows,
        &[echelon, cols, cols],
    );

    let ty = {
        let over_cols = d.pi_fv(cols_fv, nat, stmt);
        d.pi_fv(m_fv, mty, over_cols)
    };
    let value = {
        let over_cols = d.lam_fv(cols_fv, nat, proof);
        d.lam_fv(m_fv, mty, over_cols)
    };
    d.declare_theorem(p.rank_cols_zero_rows, ty, value)
}

/// Admit `Rat.nullity_zero_rows : ∀ M cols, nullity M 0 cols = cols`.
///
/// With no rows every column is free, so the nullity is the full width. This
/// is the discriminating degenerate control: `rankCols_zero_rows` alone is
/// satisfied by a `nullity` that returns `0`, and this one is not.
///
/// The proof is [`declare_rank_nullity`] read backwards through
/// [`declare_rank_cols_zero_rows`]:
///
/// ```text
/// nullity M 0 cols
///   = add 0 (nullity M 0 cols)                     (Nat.zero_add, symm)
///   = add (rankCols M 0 cols) (nullity M 0 cols)   (rankCols_zero_rows, symm, under add)
///   = cols                                         (rank_nullity)
/// ```
///
/// `Nat.add` recurses on its RIGHT argument, so `add 0 x` is NOT `x` by
/// reduction and `Nat.zero_add` is genuinely needed — the standard trap this
/// repository's guide names.
fn declare_nullity_zero_rows(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let mty = mat_ty(d);

    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let cols_fv = d.fresh_fvar();
    let cols = d.kernel().fvar(cols_fv);

    let zero_rows = d.zero();
    let nl = rnullity(d, p, m, zero_rows, cols);
    let rc = rrank_cols(d, p, m, zero_rows, cols);
    let stmt = d.eq(nl, cols);

    let proof = {
        let zero_n = d.zero();
        let zero_plus = d.add(zero_n, nl);
        let zero_add = d.prelude().zero_add;
        let h_zero_add = d.lemma(zero_add, &[nl]);
        let step_one = d.symm(zero_plus, nl, h_zero_add);

        let h_rc = d.lemma(p.rank_cols_zero_rows, &[m, cols]);
        let zero_r = d.zero();
        let h_rc_symm = d.symm(rc, zero_r, h_rc);
        let sum = d.add(rc, nl);
        let step_two = d.congr(zero_r, rc, h_rc_symm, &|d, t| d.add(t, nl));

        let step_three = d.lemma(p.rank_nullity, &[m, zero_rows, cols]);

        let (_end, proof) = d.chain(
            nl,
            &[(zero_plus, step_one), (sum, step_two), (cols, step_three)],
        );
        proof
    };

    let ty = {
        let over_cols = d.pi_fv(cols_fv, nat, stmt);
        d.pi_fv(m_fv, mty, over_cols)
    };
    let value = {
        let over_cols = d.lam_fv(cols_fv, nat, proof);
        d.lam_fv(m_fv, mty, over_cols)
    };
    d.declare_theorem(p.nullity_zero_rows, ty, value)
}
