//! The pivot-row ↔ pivot-column correspondence under the `Rat.rank =
//! Rat.rankCols` bridge (ADR-1554 obligation 4, ADR-1558 §3, ADR-1562).
//!
//! ## What the bridge needs, and in which direction
//!
//! `Rat.rank M rows cols` counts the NONZERO ROWS of `E := rowEchelon M rows
//! cols` over `[0, rows)`; `Rat.rankCols M rows cols` counts the PIVOT COLUMNS
//! over `[0, cols)`. `Nat.countRange_bij` (the cross-bound counting law, landed
//! 2026-09-02) equates two such counts given a constructive bijection between
//! the two selected sets: an injective `σ`, an inverse `τ`, two `MapsInto`
//! facts and two round-trip equations.
//!
//! The two maps are:
//!
//! ```text
//! σ = Rat.pivotColOfRow E cols     := fun r => leadingIndex E r cols
//! τ = Rat.pivotRowOfCol E rows cols := the first row < rows whose leading index is j
//! ```
//!
//! **The orientation is not free, and this file takes the one that is cheap.**
//! Applying `countRange_bij` with `p := isPivotColB` over `[0, cols)` and
//! `q := nonzeroRowB` over `[0, rows)` — i.e. `σ := pivotRowOfCol` and
//! `τ := pivotColOfRow`, columns on the LEFT — makes the injectivity
//! hypothesis FREE: `pivotRowOfCol c₁ = pivotRowOfCol c₂` gives
//! `leadingIndex E (pivotRowOfCol c₁) cols = leadingIndex E (pivotRowOfCol c₂)
//! cols`, and each side is its own column by `declare_leading_index_pivot_row_of_col`.
//! The other orientation (rows on the left) needs injectivity of `leadingIndex`
//! on the nonzero rows, which is exactly the strictly-increasing property and
//! therefore exactly obligation 4. Choosing the direction moved a hard
//! hypothesis into a free one.
//!
//! ## What is left after that choice: ONE hypothesis
//!
//! With columns on the left, four of the five hypotheses are discharged from
//! properties of the two SEARCHES alone — nothing about echelon form:
//!
//! | hypothesis | discharged by |
//! |---|---|
//! | H1 injectivity of `σ = pivotRowOfCol` | `declare_leading_index_pivot_row_of_col` |
//! | H2 `σ` maps pivot columns to nonzero rows | `declare_pivot_row_of_col_lt_rows` + the same |
//! | H4 `τ (σ c) = c` | `declare_leading_index_pivot_row_of_col` |
//! | H5 `σ (τ r) = r` | **the residue** |
//! | H3 `τ` maps nonzero rows to pivot columns | H5 + `declare_is_pivot_col_b_eq_ble` |
//!
//! and the whole of obligation 4 collapses into the single statement
//!
//! ```text
//! ∀ r, Lt r rows → nonzeroRowB E cols r = true →
//!   Eq Nat (pivotRowOfCol E rows cols (leadingIndex E r cols)) r
//! ```
//!
//! *"the FIRST row whose leading index is row `r`'s leading index is `r`
//! itself"*. That is the weakest form of obligation 4 the bridge actually
//! consumes, and it is what `declare_rank_eq_rank_cols_of_section` takes as
//! a hypothesis. `rowEchelon_isEchelon` remains open; when it lands, this
//! statement is what it has to supply, and it is strictly weaker than the full
//! echelon predicate — it says nothing about zero rows sitting last, only that
//! no earlier row shares a nonzero row's leading index.
//!
//! ## The `Bool` search and the `Nat` search are the same search
//!
//! `Rat.isPivotColB` (ADR-1558) already scans the rows for a leading index
//! equal to `j` and answers `Bool`; `Rat.pivotRowOfCol` scans the
//! same rows in the same order and answers the row itself, `rows` when there is
//! none. `declare_is_pivot_col_b_eq_ble` proves they agree —
//! `isPivotColB E rows cols j = Nat.ble (succ (pivotRowOfCol E rows cols j)) rows`
//! — by one fuel induction, and every `isPivotColB` fact this file needs goes
//! through it rather than through a second scan of its own. The identity is
//! **not** structural: in the hit branch the answer is the row index `r`, and
//! `r < rows` there comes from the outer `Nat.ble rows r = false` test, so the
//! induction does need that hypothesis (the same asymmetric-splits observation
//! `pivot_bound.rs` records).
//!
//! ## Computed, not extracted
//!
//! `pivotColOfRow` and `pivotRowOfCol` are `Definition`s the kernel reduces, so
//! `pivotRowOfCol E 3 3 1` evaluates to a row index and a wrong definition is
//! observable. The trusted gate cannot see a wrong `Definition` —
//! `pivotRowOfCol` has type `Mat → Nat → Nat → Nat → Nat` whatever it returns
//! — so `rank_bridge_tests.rs` reduces both at the six matrices the rank and
//! nullity lanes used, including the rectangular one.

use super::RatPrelude;
use super::echelon::{bool_select_at, nat_fuel_rec};
use super::matrix_det::mat_ty;
use crate::KernelError;
use crate::env::{Declaration, ReducibilityHint};
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::NatOps;

/// Delta height for `Rat.pivotColOfRow` and `Rat.pivotRowSearchAux`, one above
/// `Rat.leadingIndex`'s 58 — the same height `Rat.pivotColSearchAux` carries,
/// and for the same reason: the leading index must unfold underneath the scan.
const SEARCH_HEIGHT: u16 = 59;

/// Delta height for `Rat.pivotRowOfCol`, one above the scan it wraps — the
/// height `Rat.isPivotColB` carries.
const WRAP_HEIGHT: u16 = 60;

/// Declare everything this file builds.
///
/// # Errors
///
/// Returns the trusted gate's rejection — an `Err` means the kernel
/// **refused** a declaration, not that a script gave up.
pub(super) fn declare_rank_bridge(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    declare_pivot_col_of_row(d, p)?;
    declare_pivot_col_of_row_eq_leading_index(d, p)?;
    declare_pivot_row_search_aux(d, p)?;
    declare_pivot_row_of_col(d, p)?;
    declare_pivot_row_of_col_eq_search(d, p)?;
    Ok(())
}

// --- small shapes ----------------------------------------------------------

/// `Rat.leadingIndex E r cols`.
fn rleading_index(d: &mut IntDev<'_>, p: RatPrelude, e: ExprId, r: ExprId, cols: ExprId) -> ExprId {
    d.const_app(p.leading_index, &[e, r, cols])
}

/// `Rat.pivotColOfRow E cols r`.
pub(super) fn rpivot_col_of_row(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    e: ExprId,
    cols: ExprId,
    r: ExprId,
) -> ExprId {
    d.const_app(p.pivot_col_of_row, &[e, cols, r])
}

/// `Rat.pivotRowOfCol E rows cols j`.
pub(super) fn rpivot_row_of_col(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    e: ExprId,
    rows: ExprId,
    cols: ExprId,
    j: ExprId,
) -> ExprId {
    d.const_app(p.pivot_row_of_col, &[e, rows, cols, j])
}

// --- σ: the pivot column of a row -----------------------------------------

/// Admit `Rat.pivotColOfRow : Mat -> Nat -> Nat -> Nat`,
/// `pivotColOfRow E cols r := leadingIndex E r cols`.
///
/// The row index comes LAST so that `pivotColOfRow E cols` is already the
/// `Nat → Nat` map `Nat.countRange_bij` wants for `σ`; `leadingIndex` itself
/// takes `r` in the middle, so using it directly would put a lambda in every
/// hypothesis — and a lambda is what the counting laws cannot see through.
/// That argument-order discipline is `Rat.nonzeroRowB`'s and
/// `Rat.isPivotColB`'s, applied to a `Nat`-valued map rather than a predicate.
fn declare_pivot_col_of_row(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let mty = mat_ty(d);

    let e_fv = d.fresh_fvar();
    let e = d.kernel().fvar(e_fv);
    let cols_fv = d.fresh_fvar();
    let cols = d.kernel().fvar(cols_fv);
    let r_fv = d.fresh_fvar();
    let r = d.kernel().fvar(r_fv);

    let body = rleading_index(d, p, e, r, cols);
    let value = {
        let over_r = d.lam_fv(r_fv, nat, body);
        let over_cols = d.lam_fv(cols_fv, nat, over_r);
        d.lam_fv(e_fv, mty, over_cols)
    };
    let ty = {
        let over_r = d.arrow(nat, nat);
        let over_cols = d.arrow(nat, over_r);
        d.arrow(mty, over_cols)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.pivot_col_of_row,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(SEARCH_HEIGHT),
    })
}

/// Admit `Rat.pivotColOfRow_eq_leadingIndex : ∀ E cols r,
/// pivotColOfRow E cols r = leadingIndex E r cols`.
///
/// The defining equation, by `Eq.refl`. Every proof that has to move between
/// the `σ` of the counting law and the leading index goes through this rather
/// than unfolding a `Definition` inside a proof term.
fn declare_pivot_col_of_row_eq_leading_index(
    d: &mut IntDev<'_>,
    p: RatPrelude,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let mty = mat_ty(d);

    let e_fv = d.fresh_fvar();
    let e = d.kernel().fvar(e_fv);
    let cols_fv = d.fresh_fvar();
    let cols = d.kernel().fvar(cols_fv);
    let r_fv = d.fresh_fvar();
    let r = d.kernel().fvar(r_fv);

    let lhs = rpivot_col_of_row(d, p, e, cols, r);
    let rhs = rleading_index(d, p, e, r, cols);
    let stmt = d.eq(lhs, rhs);
    let proof = d.refl(rhs);

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
    d.declare_theorem(p.pivot_col_of_row_eq_leading_index, ty, value)
}

// --- τ: the pivot row of a column ------------------------------------------

/// Admit `Rat.pivotRowSearchAux : Mat -> Nat -> Nat -> Nat -> Nat -> Nat -> Nat`,
/// `pivotRowSearchAux E rows cols j fuel r`.
///
/// The first `r' >= r` below `rows` whose leading index is `j`, and `rows` when
/// the fuel runs out or the scan reaches the bound. Both exhaustion answers are
/// the SAME out-of-range value on purpose, exactly as `Rat.pivotSearchAux`
/// does: a caller reads "no such row" from one test and never has to
/// distinguish "searched everything" from "gave up".
///
/// This is `Rat.pivotColSearchAux`'s scan with the ANSWER changed from `Bool`
/// to the row index — same order, same bound, same fuel — which is why
/// `declare_is_pivot_col_b_eq_ble` can relate the two by a single induction
/// rather than re-deriving either.
fn declare_pivot_row_search_aux(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
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

    let inner_ty = d.arrow(nat, nat);

    let zero_case = {
        let r_fv = d.fresh_fvar();
        d.lam_fv(r_fv, nat, rows)
    };
    let succ_case = {
        let n_fv = d.fresh_fvar();
        let ih_fv = d.fresh_fvar();
        let ih = d.kernel().fvar(ih_fv);
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);

        let lead = rleading_index(d, p, e, r, cols);
        let hit = NatOps::beq(d, lead, j);
        let sr = d.succ(r);
        let recurse = d.apply(ih, &[sr]);
        let keep_looking = bool_select_at(d, nat, hit, r, recurse);
        let out_of_range = NatOps::ble(d, rows, r);
        let body = bool_select_at(d, nat, out_of_range, rows, keep_looking);

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
        let over_r = d.arrow(nat, nat);
        let over_fuel = d.arrow(nat, over_r);
        let over_j = d.arrow(nat, over_fuel);
        let over_cols = d.arrow(nat, over_j);
        let over_rows = d.arrow(nat, over_cols);
        d.arrow(mty, over_rows)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.pivot_row_search_aux,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(SEARCH_HEIGHT),
    })
}

/// Admit `Rat.pivotRowOfCol : Mat -> Nat -> Nat -> Nat -> Nat`,
/// `pivotRowOfCol E rows cols j := pivotRowSearchAux E rows cols j rows 0`.
///
/// Fuel `rows` is exact: the scan starts at `0` and stops at `rows`. The column
/// index comes LAST so `pivotRowOfCol E rows cols` is already the `Nat → Nat`
/// map the counting law wants for `σ`.
fn declare_pivot_row_of_col(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
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

    let zero_n = d.zero();
    let body = d.const_app(p.pivot_row_search_aux, &[e, rows, cols, j, rows, zero_n]);
    let value = {
        let over_j = d.lam_fv(j_fv, nat, body);
        let over_cols = d.lam_fv(cols_fv, nat, over_j);
        let over_rows = d.lam_fv(rows_fv, nat, over_cols);
        d.lam_fv(e_fv, mty, over_rows)
    };
    let ty = {
        let over_j = d.arrow(nat, nat);
        let over_cols = d.arrow(nat, over_j);
        let over_rows = d.arrow(nat, over_cols);
        d.arrow(mty, over_rows)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.pivot_row_of_col,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(WRAP_HEIGHT),
    })
}

/// Admit `Rat.pivotRowOfCol_eq_search : ∀ E rows cols j,
/// pivotRowOfCol E rows cols j = pivotRowSearchAux E rows cols j rows 0`.
///
/// The defining equation, by `Eq.refl` — the route from the wrapper to the
/// fuel induction, so no later proof has to unfold a `Definition` by hand.
fn declare_pivot_row_of_col_eq_search(
    d: &mut IntDev<'_>,
    p: RatPrelude,
) -> Result<(), KernelError> {
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

    let lhs = rpivot_row_of_col(d, p, e, rows, cols, j);
    let zero_n = d.zero();
    let rhs = d.const_app(p.pivot_row_search_aux, &[e, rows, cols, j, rows, zero_n]);
    let stmt = d.eq(lhs, rhs);
    let proof = d.refl(rhs);

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
    d.declare_theorem(p.pivot_row_of_col_eq_search, ty, value)
}
