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
use crate::nat_prelude::steps::{absurd, or_cases};

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
    declare_pivot_col_search_aux_eq_ble(d, p)?;
    declare_is_pivot_col_b_eq_ble(d, p)?;
    declare_pivot_row_of_col_lt_rows(d, p)?;
    declare_pivot_row_search_aux_leading_index(d, p)?;
    declare_leading_index_pivot_row_of_col(d, p)?;
    declare_rank_eq_rank_cols_of_pivot_section(d, p)?;
    declare_rank_le_cols_of_pivot_section(d, p)?;
    declare_rank_nullity_rows_of_pivot_section(d, p)?;
    declare_rank_cols_le_rank(d, p)?;
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

// --- devices ---------------------------------------------------------------

/// `Or (Eq Bool b true) (Eq Bool b false)` — the two-way case analysis on a
/// `Bool`, at `IntDev`.
///
/// `pivot_bound.rs` carries the same term for the same reason
/// (`nat_prelude::ops::bool_true_or_false` has a `NatDev`-specific signature
/// and this file runs at `IntDev`); it is private there.
pub(super) fn bool_cases(d: &mut IntDev<'_>, b: ExprId) -> ExprId {
    let bool_ty = d.bool_ty();
    let logic = d.prelude().logic;

    let motive = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let true_inner = d.bool_true();
        let false_inner = d.bool_false();
        let is_true = d.bool_eq(x, true_inner);
        let is_false = d.bool_eq(x, false_inner);
        let body = d.const_app(logic.or, &[is_true, is_false]);
        d.lam_fv(x_fv, bool_ty, body)
    };
    let case_true = {
        let true_ = d.bool_true();
        let false_ = d.bool_false();
        let is_true = d.bool_eq(true_, true_);
        let is_false = d.bool_eq(true_, false_);
        let refl_true = d.bool_refl(true_);
        d.const_app(logic.or_inl, &[is_true, is_false, refl_true])
    };
    let case_false = {
        let true_ = d.bool_true();
        let false_ = d.bool_false();
        let is_true = d.bool_eq(false_, true_);
        let is_false = d.bool_eq(false_, false_);
        let refl_false = d.bool_refl(false_);
        d.const_app(logic.or_inr, &[is_true, is_false, refl_false])
    };
    let level_zero = d.kernel().level_zero();
    let bool_rec = d.kernel().const_(logic.bool_rec, vec![level_zero]);
    d.apply(bool_rec, &[motive, case_false, case_true, b])
}

/// `Bool.rec.{0} motive case_false case_true b` — a bare case split at a `Prop`
/// motive, with NO hypothesis about `b`.
///
/// This is what makes a split free: it applies when both branch proofs can be
/// built without knowing which way the test went. `pivot_bound.rs` records the
/// same observation (its `le_select`), and the two splits in
/// [`declare_pivot_col_search_aux_eq_ble`]'s step case are one of each kind —
/// the inner one is free, the outer one is not.
fn bool_prop_rec(
    d: &mut IntDev<'_>,
    motive: ExprId,
    case_false: ExprId,
    case_true: ExprId,
    b: ExprId,
) -> ExprId {
    let level_zero = d.kernel().level_zero();
    let bool_rec_name = d.prelude().logic.bool_rec;
    let bool_rec = d.kernel().const_(bool_rec_name, vec![level_zero]);
    d.apply(bool_rec, &[motive, case_false, case_true, b])
}

/// `And.intro`.
fn and_intro(
    d: &mut IntDev<'_>,
    left_ty: ExprId,
    right_ty: ExprId,
    left: ExprId,
    right: ExprId,
) -> ExprId {
    let and_intro_name = d.prelude().logic.and_intro;
    d.const_app(and_intro_name, &[left_ty, right_ty, left, right])
}

/// `Eq Bool (Nat.ble (succ n) n) Bool.false` — *"`n < n` is false"*, as a
/// `Bool` equation.
///
/// The base case of [`declare_pivot_col_search_aux_eq_ble`] is exactly this:
/// with no fuel the `Bool` scan answers `false` and the `Nat` scan answers
/// `rows`, and the two agree only because `ble (succ rows) rows` is `false`.
/// `Nat` has no such equation, so it is built from `lt_irrefl` through a
/// two-way split on the `Bool` itself.
fn ble_succ_self_false(d: &mut IntDev<'_>, n: ExprId) -> ExprId {
    let b = {
        let sn = d.succ(n);
        NatOps::ble(d, sn, n)
    };
    let false_ = d.bool_false();
    let goal = d.bool_eq(b, false_);

    let true_ = d.bool_true();
    let h_true_ty = d.bool_eq(b, true_);
    let h_false_ty = d.bool_eq(b, false_);

    let left_minor = {
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let sn = d.succ(n);
        let le_of_ble = d.prelude().le_of_ble_eq_true;
        let le_proof = d.lemma(le_of_ble, &[sn, n]);
        let le_proof = d.apply(le_proof, &[h]);
        let lt_irrefl = d.prelude().lt_irrefl;
        let refutation = d.lemma(lt_irrefl, &[n]);
        let contradiction = d.apply(refutation, &[le_proof]);
        let body = absurd(d, goal, contradiction);
        d.lam_fv(h_fv, h_true_ty, body)
    };
    let right_minor = {
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        d.lam_fv(h_fv, h_false_ty, h)
    };

    let split = bool_cases(d, b);
    or_cases(
        d,
        h_true_ty,
        h_false_ty,
        goal,
        left_minor,
        right_minor,
        split,
    )
}

/// `h : Eq Bool (Nat.ble a b) Bool.false ⊢ Lt b a`.
///
/// `pivot_bound.rs`'s `le_of_ble_false` produces only `Le b a`, because it
/// splits on `Nat.le_total` and the surviving disjunct is the non-strict one.
/// The scans here need the STRICT bound — `Nat.ble rows r = false` is the only
/// place a row index is known to be in range — so this splits on
/// `Nat.lt_or_ge` instead, whose surviving disjunct is `Lt b a` directly.
fn lt_of_ble_false(d: &mut IntDev<'_>, a: ExprId, b: ExprId, h: ExprId) -> ExprId {
    let goal = NatOps::lt(d, b, a);

    let lt_ba = NatOps::lt(d, b, a);
    let le_ab = NatOps::le(d, a, b);

    let left_minor = {
        let hl_fv = d.fresh_fvar();
        let hl = d.kernel().fvar(hl_fv);
        d.lam_fv(hl_fv, lt_ba, hl)
    };
    let right_minor = {
        let hr_fv = d.fresh_fvar();
        let hr = d.kernel().fvar(hr_fv);

        let ble_eq_true_of_le = d.prelude().ble_eq_true_of_le;
        let h_true = d.lemma(ble_eq_true_of_le, &[a, b, hr]);

        let ble_ab = NatOps::ble(d, a, b);
        let true_ = d.bool_true();
        let false_ = d.bool_false();
        let h_sym = d.bool_symm(ble_ab, true_, h_true);
        let clash = d.bool_trans(true_, ble_ab, false_, h_sym, h);

        let true_ne_false = d.prelude().logic.bool_true_ne_false;
        let contradiction = d.lemma(true_ne_false, &[clash]);
        let body = absurd(d, goal, contradiction);
        d.lam_fv(hr_fv, le_ab, body)
    };

    let lt_or_ge = d.prelude().lt_or_ge;
    let split = d.lemma(lt_or_ge, &[b, a]);
    or_cases(d, lt_ba, le_ab, goal, left_minor, right_minor, split)
}

/// `h : Eq Nat x y ⊢ Eq Bool (body x) (body y)` — congruence out of `Nat` and
/// into `Bool`, which `NatOps::congr` (a `Nat → Nat` context) cannot express.
fn nat_congr_bool(
    d: &mut IntDev<'_>,
    x: ExprId,
    y: ExprId,
    h: ExprId,
    body: &dyn Fn(&mut IntDev<'_>, ExprId) -> ExprId,
) -> ExprId {
    let fx = body(d, x);
    let motive = d.eq_motive(x, &|d, t| {
        let ft = body(d, t);
        d.bool_eq(fx, ft)
    });
    let refl_case = d.bool_refl(fx);
    d.transport(x, motive, refl_case, y, h)
}

// --- the two scans are the same scan ---------------------------------------

/// Admit `Rat.pivotColSearchAux_eq_ble : ∀ E rows cols j fuel r,
/// pivotColSearchAux E rows cols j fuel r
///   = Nat.ble (succ (pivotRowSearchAux E rows cols j fuel r)) rows`.
///
/// The `Bool` scan answers `true` exactly when the `Nat` scan lands in range.
/// Induction on the fuel with the row index generalised INSIDE the motive —
/// `r` moves in the recursion, so the step instantiates its hypothesis at
/// `succ r`.
///
/// The base case is not `Eq.refl`: with no fuel the two scans answer `false`
/// and `rows`, and they agree only because `ble (succ rows) rows` is `false`
/// ([`ble_succ_self_false`]).
///
/// The step splits twice and **the two splits are not the same shape**. The
/// inner split on `Nat.beq (leadingIndex E r cols) j` is free — a bare
/// `Bool.rec` at a `Prop` motive — because both branch proofs are available
/// without knowing which way it went. The outer split on `Nat.ble rows r`
/// needs its hypothesis: in the `false` branch the `Nat` scan can still answer
/// the row index `r`, and `ble (succ r) rows = true` is exactly what
/// `ble rows r = false` buys.
fn declare_pivot_col_search_aux_eq_ble(
    d: &mut IntDev<'_>,
    p: RatPrelude,
) -> Result<(), KernelError> {
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
    let fuel_fv = d.fresh_fvar();
    let fuel = d.kernel().fvar(fuel_fv);

    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        let col = d.const_app(p.pivot_col_search_aux, &[e, rows, cols, j, x, r]);
        let row = d.const_app(p.pivot_row_search_aux, &[e, rows, cols, j, x, r]);
        let srow = d.succ(row);
        let rhs = NatOps::ble(d, srow, rows);
        let body = d.bool_eq(col, rhs);
        d.pi_fv(r_fv, nat, body)
    };
    let stmt = motive(d, fuel);

    let base = |d: &mut IntDev<'_>| -> ExprId {
        let r_fv = d.fresh_fvar();
        let eqn = ble_succ_self_false(d, rows);
        let srows = d.succ(rows);
        let ble_term = NatOps::ble(d, srows, rows);
        let false_ = d.bool_false();
        let body = d.bool_symm(ble_term, false_, eqn);
        d.lam_fv(r_fv, nat, body)
    };

    let step = |d: &mut IntDev<'_>, jf: ExprId, ih: ExprId| -> ExprId {
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);

        let lead = rleading_index(d, p, e, r, cols);
        let hit = NatOps::beq(d, lead, j);
        let sr = d.succ(r);
        let col_rec = d.const_app(p.pivot_col_search_aux, &[e, rows, cols, j, jf, sr]);
        let row_rec = d.const_app(p.pivot_row_search_aux, &[e, rows, cols, j, jf, sr]);

        let true_ = d.bool_true();
        let false_ = d.bool_false();
        let inner_col = bool_select_at(d, bool_ty, hit, true_, col_rec);
        let inner_row = bool_select_at(d, nat, hit, r, row_rec);

        let oor = NatOps::ble(d, rows, r);
        let outer_col = bool_select_at(d, bool_ty, oor, false_, inner_col);
        let outer_row = bool_select_at(d, nat, oor, rows, inner_row);
        let souter_row = d.succ(outer_row);
        let outer_rhs = NatOps::ble(d, souter_row, rows);
        let goal = d.bool_eq(outer_col, outer_rhs);

        let h_true_ty = d.bool_eq(oor, true_);
        let h_false_ty = d.bool_eq(oor, false_);

        let left_minor = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let motive_x = d.bool_eq_motive(true_, &|d, x| {
                let lhs = bool_select_at(d, bool_ty, x, false_, inner_col);
                let chosen = bool_select_at(d, nat, x, rows, inner_row);
                let schosen = d.succ(chosen);
                let rhs = NatOps::ble(d, schosen, rows);
                d.bool_eq(lhs, rhs)
            });
            let eqn = ble_succ_self_false(d, rows);
            let srows = d.succ(rows);
            let ble_term = NatOps::ble(d, srows, rows);
            let refl_case = d.bool_symm(ble_term, false_, eqn);
            let h_sym = d.bool_symm(oor, true_, h);
            let body = d.bool_transport(true_, motive_x, refl_case, oor, h_sym);
            d.lam_fv(h_fv, h_true_ty, body)
        };

        let right_minor = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);

            // `Lt r rows` -- the whole content of the outer `false` branch.
            let lt_r = lt_of_ble_false(d, rows, r, h);

            // The inner split is free: a bare `Bool.rec` at a `Prop` motive.
            let motive_hit = {
                let y_fv = d.fresh_fvar();
                let y = d.kernel().fvar(y_fv);
                let lhs = bool_select_at(d, bool_ty, y, true_, col_rec);
                let chosen = bool_select_at(d, nat, y, r, row_rec);
                let schosen = d.succ(chosen);
                let rhs = NatOps::ble(d, schosen, rows);
                let body = d.bool_eq(lhs, rhs);
                d.lam_fv(y_fv, bool_ty, body)
            };
            let case_true = {
                let ble_eq_true_of_le = d.prelude().ble_eq_true_of_le;
                let sr_inner = d.succ(r);
                let proved = d.lemma(ble_eq_true_of_le, &[sr_inner, rows, lt_r]);
                let ble_term = NatOps::ble(d, sr_inner, rows);
                d.bool_symm(ble_term, true_, proved)
            };
            let case_false = d.apply(ih, &[sr]);
            let inner_proof = bool_prop_rec(d, motive_hit, case_false, case_true, hit);

            let motive_x = d.bool_eq_motive(false_, &|d, x| {
                let lhs = bool_select_at(d, bool_ty, x, false_, inner_col);
                let chosen = bool_select_at(d, nat, x, rows, inner_row);
                let schosen = d.succ(chosen);
                let rhs = NatOps::ble(d, schosen, rows);
                d.bool_eq(lhs, rhs)
            });
            let h_sym = d.bool_symm(oor, false_, h);
            let body = d.bool_transport(false_, motive_x, inner_proof, oor, h_sym);
            d.lam_fv(h_fv, h_false_ty, body)
        };

        let split = bool_cases(d, oor);
        let body = or_cases(
            d,
            h_true_ty,
            h_false_ty,
            goal,
            left_minor,
            right_minor,
            split,
        );
        d.lam_fv(r_fv, nat, body)
    };

    let proof = d.induct(&motive, &base, &step, fuel);

    let ty = {
        let over_fuel = d.pi_fv(fuel_fv, nat, stmt);
        let over_j = d.pi_fv(j_fv, nat, over_fuel);
        let over_cols = d.pi_fv(cols_fv, nat, over_j);
        let over_rows = d.pi_fv(rows_fv, nat, over_cols);
        d.pi_fv(e_fv, mty, over_rows)
    };
    let value = {
        let over_fuel = d.lam_fv(fuel_fv, nat, proof);
        let over_j = d.lam_fv(j_fv, nat, over_fuel);
        let over_cols = d.lam_fv(cols_fv, nat, over_j);
        let over_rows = d.lam_fv(rows_fv, nat, over_cols);
        d.lam_fv(e_fv, mty, over_rows)
    };
    d.declare_theorem(p.pivot_col_search_aux_eq_ble, ty, value)
}

/// Admit `Rat.isPivotColB_eq_ble : ∀ E rows cols j,
/// isPivotColB E rows cols j = Nat.ble (succ (pivotRowOfCol E rows cols j)) rows`.
///
/// `declare_pivot_col_search_aux_eq_ble` at the fuel and start index both
/// wrappers pick. This is the bridge between ADR-1558's `Bool` pivot-column
/// test and this file's `Nat`-valued inverse, and every `isPivotColB` fact
/// below reaches the search through it.
fn declare_is_pivot_col_b_eq_ble(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
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

    let lhs = d.const_app(p.is_pivot_col_b, &[e, rows, cols, j]);
    let tau = rpivot_row_of_col(d, p, e, rows, cols, j);
    let stau = d.succ(tau);
    let rhs = NatOps::ble(d, stau, rows);
    let stmt = d.bool_eq(lhs, rhs);

    let zero_n = d.zero();
    let aux = d.lemma(p.pivot_col_search_aux_eq_ble, &[e, rows, cols, j, rows]);
    let proof = d.apply(aux, &[zero_n]);

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
    d.declare_theorem(p.is_pivot_col_b_eq_ble, ty, value)
}

/// Admit `Rat.pivotRowOfCol_lt_rows : ∀ E rows cols j,
/// isPivotColB E rows cols j = true → Lt (pivotRowOfCol E rows cols j) rows`.
///
/// One rewrite through `declare_is_pivot_col_b_eq_ble` and one
/// `Nat.le_of_ble_eq_true`: `Lt x rows` is `Le (succ x) rows` definitionally,
/// which is precisely the shape the `ble` on the right of the identity has.
fn declare_pivot_row_of_col_lt_rows(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
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

    let is_pivot = d.const_app(p.is_pivot_col_b, &[e, rows, cols, j]);
    let true_ = d.bool_true();
    let hyp_ty = d.bool_eq(is_pivot, true_);

    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let tau = rpivot_row_of_col(d, p, e, rows, cols, j);
    let stau = d.succ(tau);
    let ble_term = NatOps::ble(d, stau, rows);

    let identity = d.lemma(p.is_pivot_col_b_eq_ble, &[e, rows, cols, j]);
    let sym = d.bool_symm(is_pivot, ble_term, identity);
    let ble_true = d.bool_trans(ble_term, is_pivot, true_, sym, h);
    let le_of_ble = d.prelude().le_of_ble_eq_true;
    let body = d.lemma(le_of_ble, &[stau, rows, ble_true]);

    let concl = NatOps::lt(d, tau, rows);
    let stmt = d.arrow(hyp_ty, concl);
    let proof = d.lam_fv(h_fv, hyp_ty, body);

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
    d.declare_theorem(p.pivot_row_of_col_lt_rows, ty, value)
}

// --- what the scan found, when it found anything ---------------------------

/// Admit `Rat.pivotRowSearchAux_leadingIndex : ∀ E rows cols j fuel r,
/// Lt (pivotRowSearchAux E rows cols j fuel r) rows →
///   Eq Nat (leadingIndex E (pivotRowSearchAux E rows cols j fuel r) cols) j`.
///
/// *"If the scan landed in range, it landed on a row whose leading index is
/// `j`."* The in-range hypothesis is the whole content: both exhaustion
/// answers are `rows`, which `Nat.lt_irrefl` refutes, so the two "gave up"
/// branches are discharged without knowing anything about the matrix.
///
/// Induction on the fuel with `r` generalised inside the motive, and the
/// hypothesis carried in the motive too — this is a fuel induction whose motive
/// is an IMPLICATION, which is what makes the base case discharge by refuting
/// its own hypothesis rather than by proving a conclusion.
///
/// Unlike `declare_pivot_col_search_aux_eq_ble`, **both** splits here need
/// their hypothesis: the inner one on `Nat.beq (leadingIndex E r cols) j`
/// carries the entire conclusion in its `true` branch
/// (`Nat.eq_of_beq_eq_true`), so it cannot be a bare `Bool.rec`.
fn declare_pivot_row_search_aux_leading_index(
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
    let fuel_fv = d.fresh_fvar();
    let fuel = d.kernel().fvar(fuel_fv);

    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        let found = d.const_app(p.pivot_row_search_aux, &[e, rows, cols, j, x, r]);
        let hyp = NatOps::lt(d, found, rows);
        let lead = rleading_index(d, p, e, found, cols);
        let concl = d.eq(lead, j);
        let body = d.arrow(hyp, concl);
        d.pi_fv(r_fv, nat, body)
    };
    let stmt = motive(d, fuel);

    let base = |d: &mut IntDev<'_>| -> ExprId {
        let r_fv = d.fresh_fvar();
        let hyp = NatOps::lt(d, rows, rows);
        let lead = rleading_index(d, p, e, rows, cols);
        let concl = d.eq(lead, j);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let lt_irrefl = d.prelude().lt_irrefl;
        let refutation = d.lemma(lt_irrefl, &[rows]);
        let contradiction = d.apply(refutation, &[h]);
        let inner = absurd(d, concl, contradiction);
        let over_h = d.lam_fv(h_fv, hyp, inner);
        d.lam_fv(r_fv, nat, over_h)
    };

    let step = |d: &mut IntDev<'_>, jf: ExprId, ih: ExprId| -> ExprId {
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);

        let lead_r = rleading_index(d, p, e, r, cols);
        let hit = NatOps::beq(d, lead_r, j);
        let sr = d.succ(r);
        let row_rec = d.const_app(p.pivot_row_search_aux, &[e, rows, cols, j, jf, sr]);

        let inner_row = bool_select_at(d, nat, hit, r, row_rec);
        let oor = NatOps::ble(d, rows, r);
        let outer_row = bool_select_at(d, nat, oor, rows, inner_row);

        let goal = {
            let hyp = NatOps::lt(d, outer_row, rows);
            let lead = rleading_index(d, p, e, outer_row, cols);
            let concl = d.eq(lead, j);
            d.arrow(hyp, concl)
        };

        let true_ = d.bool_true();
        let false_ = d.bool_false();
        let h_true_ty = d.bool_eq(oor, true_);
        let h_false_ty = d.bool_eq(oor, false_);

        // The shape both branches transport in: the goal with the tested
        // `Bool` replaced by a variable.
        let outer_shape = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
            let chosen = bool_select_at(d, nat, x, rows, inner_row);
            let hyp = NatOps::lt(d, chosen, rows);
            let lead = rleading_index(d, p, e, chosen, cols);
            let concl = d.eq(lead, j);
            d.arrow(hyp, concl)
        };

        let left_minor = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let motive_x = d.bool_eq_motive(true_, &outer_shape);
            // At `oor = true` the scan answered `rows`, and `Lt rows rows` is
            // refutable -- the same discharge as the base case.
            let refl_case = {
                let hyp = NatOps::lt(d, rows, rows);
                let lead = rleading_index(d, p, e, rows, cols);
                let concl = d.eq(lead, j);
                let hh_fv = d.fresh_fvar();
                let hh = d.kernel().fvar(hh_fv);
                let lt_irrefl = d.prelude().lt_irrefl;
                let refutation = d.lemma(lt_irrefl, &[rows]);
                let contradiction = d.apply(refutation, &[hh]);
                let inner = absurd(d, concl, contradiction);
                d.lam_fv(hh_fv, hyp, inner)
            };
            let h_sym = d.bool_symm(oor, true_, h);
            let body = d.bool_transport(true_, motive_x, refl_case, oor, h_sym);
            d.lam_fv(h_fv, h_true_ty, body)
        };

        let right_minor = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);

            let inner_shape = |d: &mut IntDev<'_>, y: ExprId| -> ExprId {
                let chosen = bool_select_at(d, nat, y, r, row_rec);
                let hyp = NatOps::lt(d, chosen, rows);
                let lead = rleading_index(d, p, e, chosen, cols);
                let concl = d.eq(lead, j);
                d.arrow(hyp, concl)
            };

            let hit_true_ty = d.bool_eq(hit, true_);
            let hit_false_ty = d.bool_eq(hit, false_);
            let inner_goal = inner_shape(d, hit);

            let hit_left = {
                let hh_fv = d.fresh_fvar();
                let hh = d.kernel().fvar(hh_fv);
                let motive_y = d.bool_eq_motive(true_, &inner_shape);
                let refl_case = {
                    let hyp = NatOps::lt(d, r, rows);
                    let ignored_fv = d.fresh_fvar();
                    let eq_of_beq = d.prelude().eq_of_beq_eq_true;
                    let proved = d.lemma(eq_of_beq, &[lead_r, j, hh]);
                    d.lam_fv(ignored_fv, hyp, proved)
                };
                let hh_sym = d.bool_symm(hit, true_, hh);
                let body = d.bool_transport(true_, motive_y, refl_case, hit, hh_sym);
                d.lam_fv(hh_fv, hit_true_ty, body)
            };
            let hit_right = {
                let hh_fv = d.fresh_fvar();
                let hh = d.kernel().fvar(hh_fv);
                let motive_y = d.bool_eq_motive(false_, &inner_shape);
                let refl_case = d.apply(ih, &[sr]);
                let hh_sym = d.bool_symm(hit, false_, hh);
                let body = d.bool_transport(false_, motive_y, refl_case, hit, hh_sym);
                d.lam_fv(hh_fv, hit_false_ty, body)
            };

            let hit_split = bool_cases(d, hit);
            let inner_proof = or_cases(
                d,
                hit_true_ty,
                hit_false_ty,
                inner_goal,
                hit_left,
                hit_right,
                hit_split,
            );

            let motive_x = d.bool_eq_motive(false_, &outer_shape);
            let h_sym = d.bool_symm(oor, false_, h);
            let body = d.bool_transport(false_, motive_x, inner_proof, oor, h_sym);
            d.lam_fv(h_fv, h_false_ty, body)
        };

        let split = bool_cases(d, oor);
        let body = or_cases(
            d,
            h_true_ty,
            h_false_ty,
            goal,
            left_minor,
            right_minor,
            split,
        );
        d.lam_fv(r_fv, nat, body)
    };

    let proof = d.induct(&motive, &base, &step, fuel);

    let ty = {
        let over_fuel = d.pi_fv(fuel_fv, nat, stmt);
        let over_j = d.pi_fv(j_fv, nat, over_fuel);
        let over_cols = d.pi_fv(cols_fv, nat, over_j);
        let over_rows = d.pi_fv(rows_fv, nat, over_cols);
        d.pi_fv(e_fv, mty, over_rows)
    };
    let value = {
        let over_fuel = d.lam_fv(fuel_fv, nat, proof);
        let over_j = d.lam_fv(j_fv, nat, over_fuel);
        let over_cols = d.lam_fv(cols_fv, nat, over_j);
        let over_rows = d.lam_fv(rows_fv, nat, over_cols);
        d.lam_fv(e_fv, mty, over_rows)
    };
    d.declare_theorem(p.pivot_row_search_aux_leading_index, ty, value)
}

/// Admit `Rat.leadingIndex_pivotRowOfCol : ∀ E rows cols j,
/// isPivotColB E rows cols j = true →
///   Eq Nat (leadingIndex E (pivotRowOfCol E rows cols j) cols) j`.
///
/// **This is the round trip that makes the bridge's orientation the cheap
/// one.** It says `σ` (the pivot row of a column) is a SECTION of the leading
/// index on the pivot columns, which gives three of the counting law's five
/// hypotheses at once: injectivity of `σ` (apply the leading index to both
/// sides of `σ c₁ = σ c₂`), the second component of `σ`'s `MapsInto` (the
/// leading index of `σ c` is `c`, which is below `cols`), and the round trip
/// `τ (σ c) = c` verbatim.
///
/// `declare_pivot_row_search_aux_leading_index` at the fuel and start index
/// `pivotRowOfCol` picks, with the in-range hypothesis supplied by
/// `declare_pivot_row_of_col_lt_rows`.
fn declare_leading_index_pivot_row_of_col(
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

    let is_pivot = d.const_app(p.is_pivot_col_b, &[e, rows, cols, j]);
    let true_ = d.bool_true();
    let hyp_ty = d.bool_eq(is_pivot, true_);

    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let tau = rpivot_row_of_col(d, p, e, rows, cols, j);
    let lead = rleading_index(d, p, e, tau, cols);
    let concl = d.eq(lead, j);
    let stmt = d.arrow(hyp_ty, concl);

    let in_range = d.lemma(p.pivot_row_of_col_lt_rows, &[e, rows, cols, j, h]);
    let zero_n = d.zero();
    let aux = d.lemma(
        p.pivot_row_search_aux_leading_index,
        &[e, rows, cols, j, rows],
    );
    let at_zero = d.apply(aux, &[zero_n]);
    let body = d.apply(at_zero, &[in_range]);
    let proof = d.lam_fv(h_fv, hyp_ty, body);

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
    d.declare_theorem(p.leading_index_pivot_row_of_col, ty, value)
}

// --- the bridge ------------------------------------------------------------

/// `Rat.rowEchelon M rows cols`.
fn row_echelon(d: &mut IntDev<'_>, p: RatPrelude, m: ExprId, rows: ExprId, cols: ExprId) -> ExprId {
    d.const_app(p.row_echelon, &[m, rows, cols])
}

/// The **section hypothesis**: `∀ r, Lt r rows → nonzeroRowB E cols r = true →
/// pivotRowOfCol E rows cols (pivotColOfRow E cols r) = r`.
///
/// *"The first row whose leading index is row `r`'s leading index is `r`
/// itself."* This is the ONE thing the bridge cannot get from the scans, and
/// the weakest form of ADR-1554's obligation 4 it consumes: it says nothing
/// about zero rows sitting last, only that no earlier NONZERO row shares a
/// nonzero row's leading index.
///
/// It is written out inline and is deliberately **not** a `Definition`. A named
/// `Prop` here could be well-typed and mean something else; an inline Pi cannot.
fn pivot_section_ty(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    e: ExprId,
    rows: ExprId,
    cols: ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let true_ = d.bool_true();

    let r_fv = d.fresh_fvar();
    let r = d.kernel().fvar(r_fv);

    let sigma_r = rpivot_col_of_row(d, p, e, cols, r);
    let back = rpivot_row_of_col(d, p, e, rows, cols, sigma_r);
    let concl = d.eq(back, r);

    let nonzero = d.const_app(p.nonzero_row_b, &[e, cols, r]);
    let selected = d.bool_eq(nonzero, true_);
    let step_sel = d.arrow(selected, concl);
    let in_range = NatOps::lt(d, r, rows);
    let inner = d.arrow(in_range, step_sel);
    d.pi_fv(r_fv, nat, inner)
}

/// Admit `Rat.rank_eq_rankCols_of_pivotSection : ∀ M rows cols,
/// (the section hypothesis) → Eq Nat (rank M rows cols) (rankCols M rows cols)`.
///
/// **The bridge**, through `Nat.countRange_bij` with the COLUMNS as the
/// left-hand count — `p := isPivotColB E rows cols` over `[0, cols)`,
/// `q := nonzeroRowB E cols` over `[0, rows)`, `σ := pivotRowOfCol E rows cols`
/// and `τ := pivotColOfRow E cols`.
///
/// Four of the five hypotheses come from
/// `declare_leading_index_pivot_row_of_col` and
/// `declare_pivot_row_of_col_lt_rows` and know nothing about echelon form:
///
/// - **injectivity of `σ`** — apply the leading index to both sides of
///   `σ c₁ = σ c₂`; each side is its own column, so `c₁ = c₂`. Taking the ROWS
///   as the left-hand count instead would need injectivity of the leading index
///   on the nonzero rows, which IS obligation 4 — the orientation is what makes
///   this free.
/// - **`σ`'s `MapsInto`** — `Lt (σ c) rows` is the range bound, and
///   `nonzeroRowB E cols (σ c)` is `Nat.ble (succ c) cols` once the round trip
///   rewrites the leading index, which `Lt c cols` settles.
/// - **`τ (σ c) = c`** — the round trip verbatim, since `pivotColOfRow E cols`
///   is the leading index.
/// - **`τ`'s range half** — `Lt (τ r) cols` is `nonzeroRowB E cols r = true`
///   read through `Rat.nonzeroRowB_eq_ble` and `Nat.le_of_ble_eq_true`.
///
/// The section hypothesis pays for the remaining one and a half: the round trip
/// `σ (τ r) = r` verbatim, and — through `declare_is_pivot_col_b_eq_ble` —
/// the selected half of `τ`'s `MapsInto`, because `isPivotColB E rows cols
/// (τ r)` is `Nat.ble (succ (σ (τ r))) rows`, i.e. `Nat.ble (succ r) rows`.
#[allow(clippy::too_many_lines)]
fn declare_rank_eq_rank_cols_of_pivot_section(
    d: &mut IntDev<'_>,
    p: RatPrelude,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let mty = mat_ty(d);
    let true_ = d.bool_true();

    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let rows_fv = d.fresh_fvar();
    let rows = d.kernel().fvar(rows_fv);
    let cols_fv = d.fresh_fvar();
    let cols = d.kernel().fvar(cols_fv);

    let e = row_echelon(d, p, m, rows, cols);

    let sec_ty = pivot_section_ty(d, p, e, rows, cols);
    let sec_fv = d.fresh_fvar();
    let sec = d.kernel().fvar(sec_fv);

    // The four arguments of the counting law.
    let pred_cols = d.const_app(p.is_pivot_col_b, &[e, rows, cols]);
    let pred_rows = d.const_app(p.nonzero_row_b, &[e, cols]);
    let sigma = d.const_app(p.pivot_row_of_col, &[e, rows, cols]);
    let tau = d.const_app(p.pivot_col_of_row, &[e, cols]);

    // H1: `σ` is injective on the pivot columns.
    let h1 = {
        let c1_fv = d.fresh_fvar();
        let c1 = d.kernel().fvar(c1_fv);
        let c2_fv = d.fresh_fvar();
        let c2 = d.kernel().fvar(c2_fv);

        let lt1_ty = NatOps::lt(d, c1, cols);
        let sel1 = d.const_app(p.is_pivot_col_b, &[e, rows, cols, c1]);
        let sel1_ty = d.bool_eq(sel1, true_);
        let lt2_ty = NatOps::lt(d, c2, cols);
        let sel2 = d.const_app(p.is_pivot_col_b, &[e, rows, cols, c2]);
        let sel2_ty = d.bool_eq(sel2, true_);

        let s1 = rpivot_row_of_col(d, p, e, rows, cols, c1);
        let s2 = rpivot_row_of_col(d, p, e, rows, cols, c2);
        let heq_ty = d.eq(s1, s2);

        let lt1_fv = d.fresh_fvar();
        let sel1_fv = d.fresh_fvar();
        let hp1 = d.kernel().fvar(sel1_fv);
        let lt2_fv = d.fresh_fvar();
        let sel2_fv = d.fresh_fvar();
        let hp2 = d.kernel().fvar(sel2_fv);
        let heq_fv = d.fresh_fvar();
        let heq = d.kernel().fvar(heq_fv);

        let l1 = rleading_index(d, p, e, s1, cols);
        let l2 = rleading_index(d, p, e, s2, cols);
        let round1 = d.lemma(p.leading_index_pivot_row_of_col, &[e, rows, cols, c1, hp1]);
        let round2 = d.lemma(p.leading_index_pivot_row_of_col, &[e, rows, cols, c2, hp2]);
        let moved = d.congr(s1, s2, heq, &|d, x| rleading_index(d, p, e, x, cols));
        let back1 = d.symm(l1, c1, round1);
        let to_l2 = d.trans(c1, l1, l2, back1, moved);
        let body = d.trans(c1, l2, c2, to_l2, round2);

        let over_heq = d.lam_fv(heq_fv, heq_ty, body);
        let over_sel2 = d.lam_fv(sel2_fv, sel2_ty, over_heq);
        let over_lt2 = d.lam_fv(lt2_fv, lt2_ty, over_sel2);
        let over_sel1 = d.lam_fv(sel1_fv, sel1_ty, over_lt2);
        let over_lt1 = d.lam_fv(lt1_fv, lt1_ty, over_sel1);
        let over_c2 = d.lam_fv(c2_fv, nat, over_lt1);
        d.lam_fv(c1_fv, nat, over_c2)
    };

    // H2: `σ` sends a pivot column to a nonzero row.
    let h2 = {
        let c_fv = d.fresh_fvar();
        let c = d.kernel().fvar(c_fv);
        let lt_ty = NatOps::lt(d, c, cols);
        let sel = d.const_app(p.is_pivot_col_b, &[e, rows, cols, c]);
        let sel_ty = d.bool_eq(sel, true_);

        let lt_fv = d.fresh_fvar();
        let hlt = d.kernel().fvar(lt_fv);
        let sel_fv = d.fresh_fvar();
        let hp = d.kernel().fvar(sel_fv);

        let s = rpivot_row_of_col(d, p, e, rows, cols, c);
        let left_ty = NatOps::lt(d, s, rows);
        let left = d.lemma(p.pivot_row_of_col_lt_rows, &[e, rows, cols, c, hp]);

        let nonzero = d.const_app(p.nonzero_row_b, &[e, cols, s]);
        let right_ty = d.bool_eq(nonzero, true_);

        let l = rleading_index(d, p, e, s, cols);
        let sl = d.succ(l);
        let ble_l = NatOps::ble(d, sl, cols);
        let unfold = d.lemma(p.nonzero_row_b_eq_ble, &[e, cols, s]);
        let round = d.lemma(p.leading_index_pivot_row_of_col, &[e, rows, cols, c, hp]);
        let rewritten = nat_congr_bool(d, l, c, round, &|d, x| {
            let sx = d.succ(x);
            NatOps::ble(d, sx, cols)
        });
        let sc = d.succ(c);
        let ble_c = NatOps::ble(d, sc, cols);
        let ble_true_name = d.prelude().ble_eq_true_of_le;
        let ble_true = d.lemma(ble_true_name, &[sc, cols, hlt]);
        let step1 = d.bool_trans(nonzero, ble_l, ble_c, unfold, rewritten);
        let right = d.bool_trans(nonzero, ble_c, true_, step1, ble_true);

        let pair = and_intro(d, left_ty, right_ty, left, right);
        let over_sel = d.lam_fv(sel_fv, sel_ty, pair);
        let over_lt = d.lam_fv(lt_fv, lt_ty, over_sel);
        d.lam_fv(c_fv, nat, over_lt)
    };

    // H3: `τ` sends a nonzero row to a pivot column.
    let h3 = {
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        let lt_ty = NatOps::lt(d, r, rows);
        let nonzero = d.const_app(p.nonzero_row_b, &[e, cols, r]);
        let sel_ty = d.bool_eq(nonzero, true_);

        let lt_fv = d.fresh_fvar();
        let hlt = d.kernel().fvar(lt_fv);
        let sel_fv = d.fresh_fvar();
        let hq = d.kernel().fvar(sel_fv);

        let t = rpivot_col_of_row(d, p, e, cols, r);
        let left_ty = NatOps::lt(d, t, cols);
        let left = {
            let l = rleading_index(d, p, e, r, cols);
            let sl = d.succ(l);
            let ble_l = NatOps::ble(d, sl, cols);
            let unfold = d.lemma(p.nonzero_row_b_eq_ble, &[e, cols, r]);
            let sym = d.bool_symm(nonzero, ble_l, unfold);
            let ble_true = d.bool_trans(ble_l, nonzero, true_, sym, hq);
            let le_of_ble = d.prelude().le_of_ble_eq_true;
            d.lemma(le_of_ble, &[sl, cols, ble_true])
        };

        let is_pivot = d.const_app(p.is_pivot_col_b, &[e, rows, cols, t]);
        let right_ty = d.bool_eq(is_pivot, true_);
        let right = {
            let st = rpivot_row_of_col(d, p, e, rows, cols, t);
            let sst = d.succ(st);
            let ble_st = NatOps::ble(d, sst, rows);
            let identity = d.lemma(p.is_pivot_col_b_eq_ble, &[e, rows, cols, t]);
            let section = d.apply(sec, &[r, hlt, hq]);
            let rewritten = nat_congr_bool(d, st, r, section, &|d, x| {
                let sx = d.succ(x);
                NatOps::ble(d, sx, rows)
            });
            let sr = d.succ(r);
            let ble_r = NatOps::ble(d, sr, rows);
            let ble_true_name = d.prelude().ble_eq_true_of_le;
            let ble_true = d.lemma(ble_true_name, &[sr, rows, hlt]);
            let step1 = d.bool_trans(is_pivot, ble_st, ble_r, identity, rewritten);
            d.bool_trans(is_pivot, ble_r, true_, step1, ble_true)
        };

        let pair = and_intro(d, left_ty, right_ty, left, right);
        let over_sel = d.lam_fv(sel_fv, sel_ty, pair);
        let over_lt = d.lam_fv(lt_fv, lt_ty, over_sel);
        d.lam_fv(r_fv, nat, over_lt)
    };

    // H4: `τ (σ c) = c` -- the round trip verbatim.
    let h4 = {
        let c_fv = d.fresh_fvar();
        let c = d.kernel().fvar(c_fv);
        let lt_ty = NatOps::lt(d, c, cols);
        let sel = d.const_app(p.is_pivot_col_b, &[e, rows, cols, c]);
        let sel_ty = d.bool_eq(sel, true_);

        let lt_fv = d.fresh_fvar();
        let sel_fv = d.fresh_fvar();
        let hp = d.kernel().fvar(sel_fv);

        let body = d.lemma(p.leading_index_pivot_row_of_col, &[e, rows, cols, c, hp]);
        let over_sel = d.lam_fv(sel_fv, sel_ty, body);
        let over_lt = d.lam_fv(lt_fv, lt_ty, over_sel);
        d.lam_fv(c_fv, nat, over_lt)
    };

    // H5: `σ (τ r) = r` -- the section hypothesis verbatim.
    let h5 = {
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        let lt_ty = NatOps::lt(d, r, rows);
        let nonzero = d.const_app(p.nonzero_row_b, &[e, cols, r]);
        let sel_ty = d.bool_eq(nonzero, true_);

        let lt_fv = d.fresh_fvar();
        let hlt = d.kernel().fvar(lt_fv);
        let sel_fv = d.fresh_fvar();
        let hq = d.kernel().fvar(sel_fv);

        let body = d.apply(sec, &[r, hlt, hq]);
        let over_sel = d.lam_fv(sel_fv, sel_ty, body);
        let over_lt = d.lam_fv(lt_fv, lt_ty, over_sel);
        d.lam_fv(r_fv, nat, over_lt)
    };

    let bij_name = d.prelude().count_range_bij;
    let bij = d.lemma(
        bij_name,
        &[
            pred_cols, pred_rows, sigma, tau, cols, rows, h1, h2, h3, h4, h5,
        ],
    );

    let count_range = d.prelude().count_range;
    let lhs_cols = d.const_app(count_range, &[pred_cols, cols]);
    let lhs_rows = d.const_app(count_range, &[pred_rows, rows]);
    let flipped = d.symm(lhs_cols, lhs_rows, bij);

    let rank_term = d.const_app(p.rank, &[m, rows, cols]);
    let rank_cols_term = d.const_app(p.rank_cols, &[m, rows, cols]);
    let concl = d.eq(rank_term, rank_cols_term);
    let stmt = d.arrow(sec_ty, concl);
    let proof = d.lam_fv(sec_fv, sec_ty, flipped);

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
    d.declare_theorem(p.rank_eq_rank_cols_of_pivot_section, ty, value)
}

/// Admit `Rat.rank_le_cols_of_pivotSection : ∀ M rows cols,
/// (the section hypothesis) → Le (rank M rows cols) cols`.
///
/// **The bound ADR-1555 left open**, now free from the bridge. `rankCols ≤
/// cols` was already one `Nat.countRange_le` — a count over `[0, cols)` cannot
/// exceed `cols` whatever the predicate does — and the bridge transports it to
/// the row form. Nothing is re-proved; the asymmetry ADR-1558 recorded is
/// exactly the asymmetry the bridge removes.
fn declare_rank_le_cols_of_pivot_section(
    d: &mut IntDev<'_>,
    p: RatPrelude,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let mty = mat_ty(d);

    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let rows_fv = d.fresh_fvar();
    let rows = d.kernel().fvar(rows_fv);
    let cols_fv = d.fresh_fvar();
    let cols = d.kernel().fvar(cols_fv);

    let e = row_echelon(d, p, m, rows, cols);
    let sec_ty = pivot_section_ty(d, p, e, rows, cols);
    let sec_fv = d.fresh_fvar();
    let sec = d.kernel().fvar(sec_fv);

    let rank_term = d.const_app(p.rank, &[m, rows, cols]);
    let rank_cols_term = d.const_app(p.rank_cols, &[m, rows, cols]);
    let concl = NatOps::le(d, rank_term, cols);

    let bridge = d.lemma(p.rank_eq_rank_cols_of_pivot_section, &[m, rows, cols, sec]);
    let flipped = d.symm(rank_term, rank_cols_term, bridge);
    let bound = d.lemma(p.rank_cols_le_cols, &[m, rows, cols]);
    let motive = d.eq_motive(rank_cols_term, &|d, x| NatOps::le(d, x, cols));
    let body = d.transport(rank_cols_term, motive, bound, rank_term, flipped);

    let stmt = d.arrow(sec_ty, concl);
    let proof = d.lam_fv(sec_fv, sec_ty, body);

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
    d.declare_theorem(p.rank_le_cols_of_pivot_section, ty, value)
}

/// Admit `Rat.rank_nullity_rows_of_pivotSection : ∀ M rows cols,
/// (the section hypothesis) →
///   Eq Nat (Nat.add (rank M rows cols) (nullity M rows cols)) cols`.
///
/// **Rank-nullity in the ROW form** — the form the dominance document would
/// quote, where `rank` is the number of independent rows rather than the number
/// of pivot columns. ADR-1558 landed the column form and said the obligation
/// was *relocated, entirely, into one bridge*; this is the receipt for that
/// claim: the row form is `Rat.rank_nullity` with `rankCols` rewritten to
/// `rank`, and nothing else.
fn declare_rank_nullity_rows_of_pivot_section(
    d: &mut IntDev<'_>,
    p: RatPrelude,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let mty = mat_ty(d);

    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let rows_fv = d.fresh_fvar();
    let rows = d.kernel().fvar(rows_fv);
    let cols_fv = d.fresh_fvar();
    let cols = d.kernel().fvar(cols_fv);

    let e = row_echelon(d, p, m, rows, cols);
    let sec_ty = pivot_section_ty(d, p, e, rows, cols);
    let sec_fv = d.fresh_fvar();
    let sec = d.kernel().fvar(sec_fv);

    let rank_term = d.const_app(p.rank, &[m, rows, cols]);
    let rank_cols_term = d.const_app(p.rank_cols, &[m, rows, cols]);
    let nullity_term = d.const_app(p.nullity, &[m, rows, cols]);
    let sum = d.add(rank_term, nullity_term);
    let concl = d.eq(sum, cols);

    let bridge = d.lemma(p.rank_eq_rank_cols_of_pivot_section, &[m, rows, cols, sec]);
    let flipped = d.symm(rank_term, rank_cols_term, bridge);
    let column_form = d.lemma(p.rank_nullity, &[m, rows, cols]);
    let motive = d.eq_motive(rank_cols_term, &|d, x| {
        let s = d.add(x, nullity_term);
        d.eq(s, cols)
    });
    let body = d.transport(rank_cols_term, motive, column_form, rank_term, flipped);

    let stmt = d.arrow(sec_ty, concl);
    let proof = d.lam_fv(sec_fv, sec_ty, body);

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
    d.declare_theorem(p.rank_nullity_rows_of_pivot_section, ty, value)
}

/// Admit `Rat.rankCols_le_rank : ∀ M rows cols,
/// Le (rankCols M rows cols) (rank M rows cols)` — **with no hypothesis at
/// all** (ADR-1593).
///
/// The consumer of `Nat.countRange_le_of_injOn`, and the point of that lemma
/// stated in one line: the bridge above needs a BIJECTION and therefore pays
/// the section hypothesis for `σ (τ r) = r` and for the selected half of `τ`'s
/// `MapsInto`; an INEQUALITY needs only the INJECTION, and `H1` and `H2` are
/// exactly the two hypotheses
/// [`declare_rank_eq_rank_cols_of_pivot_section`]'s own table records as
/// discharged from the two SEARCHES alone, knowing nothing about echelon form.
/// So `τ` never appears here, the section hypothesis never appears here, and
/// the two hypotheses are re-derived verbatim from
/// `declare_leading_index_pivot_row_of_col` and
/// `declare_pivot_row_of_col_lt_rows`.
///
/// The direction is the useful one: `Rat.rankCols_le_cols` is free
/// (`Nat.countRange_le`), so this gives `rankCols ≤ rank` unconditionally while
/// the reverse — `rank ≤ rankCols`, which is what bounds `rank` by `cols` —
/// still needs the section, because in that orientation injectivity of the
/// leading index on the nonzero rows IS obligation 4. Two rows sharing a
/// leading index really can make `rank` exceed `rankCols`; nothing can be said
/// about that direction without the echelon property, and this lemma does not
/// pretend to.
fn declare_rank_cols_le_rank(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let mty = mat_ty(d);
    let true_ = d.bool_true();

    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let rows_fv = d.fresh_fvar();
    let rows = d.kernel().fvar(rows_fv);
    let cols_fv = d.fresh_fvar();
    let cols = d.kernel().fvar(cols_fv);

    let e = row_echelon(d, p, m, rows, cols);

    let pred_cols = d.const_app(p.is_pivot_col_b, &[e, rows, cols]);
    let pred_rows = d.const_app(p.nonzero_row_b, &[e, cols]);
    let sigma = d.const_app(p.pivot_row_of_col, &[e, rows, cols]);

    // H1: `σ` is injective on the pivot columns — apply the leading index to
    // both sides of `σ c₁ = σ c₂`; each side is its own column.
    let h1 = {
        let c1_fv = d.fresh_fvar();
        let c1 = d.kernel().fvar(c1_fv);
        let c2_fv = d.fresh_fvar();
        let c2 = d.kernel().fvar(c2_fv);

        let lt1_ty = NatOps::lt(d, c1, cols);
        let sel1 = d.const_app(p.is_pivot_col_b, &[e, rows, cols, c1]);
        let sel1_ty = d.bool_eq(sel1, true_);
        let lt2_ty = NatOps::lt(d, c2, cols);
        let sel2 = d.const_app(p.is_pivot_col_b, &[e, rows, cols, c2]);
        let sel2_ty = d.bool_eq(sel2, true_);

        let s1 = rpivot_row_of_col(d, p, e, rows, cols, c1);
        let s2 = rpivot_row_of_col(d, p, e, rows, cols, c2);
        let heq_ty = d.eq(s1, s2);

        let lt1_fv = d.fresh_fvar();
        let sel1_fv = d.fresh_fvar();
        let hp1 = d.kernel().fvar(sel1_fv);
        let lt2_fv = d.fresh_fvar();
        let sel2_fv = d.fresh_fvar();
        let hp2 = d.kernel().fvar(sel2_fv);
        let heq_fv = d.fresh_fvar();
        let heq = d.kernel().fvar(heq_fv);

        let l1 = rleading_index(d, p, e, s1, cols);
        let l2 = rleading_index(d, p, e, s2, cols);
        let round1 = d.lemma(p.leading_index_pivot_row_of_col, &[e, rows, cols, c1, hp1]);
        let round2 = d.lemma(p.leading_index_pivot_row_of_col, &[e, rows, cols, c2, hp2]);
        let moved = d.congr(s1, s2, heq, &|d, x| rleading_index(d, p, e, x, cols));
        let back1 = d.symm(l1, c1, round1);
        let to_l2 = d.trans(c1, l1, l2, back1, moved);
        let body = d.trans(c1, l2, c2, to_l2, round2);

        let over_heq = d.lam_fv(heq_fv, heq_ty, body);
        let over_sel2 = d.lam_fv(sel2_fv, sel2_ty, over_heq);
        let over_lt2 = d.lam_fv(lt2_fv, lt2_ty, over_sel2);
        let over_sel1 = d.lam_fv(sel1_fv, sel1_ty, over_lt2);
        let over_lt1 = d.lam_fv(lt1_fv, lt1_ty, over_sel1);
        let over_c2 = d.lam_fv(c2_fv, nat, over_lt1);
        d.lam_fv(c1_fv, nat, over_c2)
    };

    // H2: `σ` sends a pivot column to a nonzero row.
    let h2 = {
        let c_fv = d.fresh_fvar();
        let c = d.kernel().fvar(c_fv);
        let lt_ty = NatOps::lt(d, c, cols);
        let sel = d.const_app(p.is_pivot_col_b, &[e, rows, cols, c]);
        let sel_ty = d.bool_eq(sel, true_);

        let lt_fv = d.fresh_fvar();
        let hlt = d.kernel().fvar(lt_fv);
        let sel_fv = d.fresh_fvar();
        let hp = d.kernel().fvar(sel_fv);

        let s = rpivot_row_of_col(d, p, e, rows, cols, c);
        let left_ty = NatOps::lt(d, s, rows);
        let left = d.lemma(p.pivot_row_of_col_lt_rows, &[e, rows, cols, c, hp]);

        let nonzero = d.const_app(p.nonzero_row_b, &[e, cols, s]);
        let right_ty = d.bool_eq(nonzero, true_);

        let l = rleading_index(d, p, e, s, cols);
        let sl = d.succ(l);
        let ble_l = NatOps::ble(d, sl, cols);
        let unfold = d.lemma(p.nonzero_row_b_eq_ble, &[e, cols, s]);
        let round = d.lemma(p.leading_index_pivot_row_of_col, &[e, rows, cols, c, hp]);
        let rewritten = nat_congr_bool(d, l, c, round, &|d, x| {
            let sx = d.succ(x);
            NatOps::ble(d, sx, cols)
        });
        let sc = d.succ(c);
        let ble_c = NatOps::ble(d, sc, cols);
        let ble_true_name = d.prelude().ble_eq_true_of_le;
        let ble_true = d.lemma(ble_true_name, &[sc, cols, hlt]);
        let step1 = d.bool_trans(nonzero, ble_l, ble_c, unfold, rewritten);
        let right = d.bool_trans(nonzero, ble_c, true_, step1, ble_true);

        let pair = and_intro(d, left_ty, right_ty, left, right);
        let over_sel = d.lam_fv(sel_fv, sel_ty, pair);
        let over_lt = d.lam_fv(lt_fv, lt_ty, over_sel);
        d.lam_fv(c_fv, nat, over_lt)
    };

    let le_name = d.prelude().count_range_le_of_inj_on;
    let body = d.lemma(le_name, &[pred_cols, pred_rows, sigma, cols, rows, h1, h2]);

    let rank_term = d.const_app(p.rank, &[m, rows, cols]);
    let rank_cols_term = d.const_app(p.rank_cols, &[m, rows, cols]);
    let concl = NatOps::le(d, rank_cols_term, rank_term);

    let ty = {
        let over_cols = d.pi_fv(cols_fv, nat, concl);
        let over_rows = d.pi_fv(rows_fv, nat, over_cols);
        d.pi_fv(m_fv, mty, over_rows)
    };
    let value = {
        let over_cols = d.lam_fv(cols_fv, nat, body);
        let over_rows = d.lam_fv(rows_fv, nat, over_cols);
        d.lam_fv(m_fv, mty, over_rows)
    };
    d.declare_theorem(p.rank_cols_le_rank, ty, value)
}
