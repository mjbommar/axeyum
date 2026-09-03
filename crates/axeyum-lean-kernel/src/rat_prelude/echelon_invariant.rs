//! ADR-1554 **obligation 4**: Gaussian elimination lands in row-echelon form.
//!
//! ```text
//! Rat.rowEchelon_isEchelon : ∀ M rows cols,
//!   Eq Bool (isEchelon (rowEchelon M rows cols) rows cols) true
//! ```
//!
//! ADR-1554 sized this as "at least a lane on its own and probably two" and
//! ADR-1571 §3 re-sized it from measurement as four prerequisite lemmas plus an
//! invariant plus two inductions. Three prerequisites landed in ADR-1571; the
//! fourth (`Rat.rowSwap_preserves_zero_range`), two more that turned out to be
//! needed (`Rat.leadingIndex_congr_row` and `Rat.clearBelow_rowSwap_off`), the
//! invariant and the inductions are all here.
//!
//! ## The invariant, and why it is built in Rust rather than declared
//!
//! [`invariant_hyps`] builds the five clauses `echelonAux rows cols fuel M pr
//! pc` maintains, as hypothesis TYPES rather than as a named `Prop`. ADR-1562
//! §2's rule applies: *a named `Definition` could be well-typed and mean
//! something else*, and a reader would have to unfold it to find out. A Rust
//! builder gives the same single place to read while every theorem's type still
//! carries the clauses literally.
//!
//! ```text
//! H0 : Le pc cols
//! H1 : ∀ r, Lt (succ r) pr → echelonStepOk (leadingIndex M r cols)
//!                              (leadingIndex M (succ r) cols) cols = true
//! H2 : ∀ r, Lt r pr → Lt (leadingIndex M r cols) pc
//! H3 : ∀ s c, Le pr s → Lt s rows → Lt c pc → Eq Rat (M s c) Rat.zero
//! H4 : Le cols (Nat.add pc fuel)
//! ```
//!
//! **H0 is not implied by H4.** H4 bounds `pc` from below through the fuel; the
//! exit branch needs the upper bound, because it reads `Lt (leadingIndex …) pc`
//! off H2 and has to turn it into `Lt … cols`.
//!
//! ## The exit derivation is folded INTO the induction
//!
//! ADR-1571 §3 listed the invariant's preservation and the exit derivation as
//! two separate inductions. They are one here: the conclusion carried at every
//! fuel level is already `isEchelon … = true`, so each of the three leaves that
//! stop the loop discharges it from the invariant directly and **nothing ever
//! has to name the final cursors**. That is the sizing correction this module
//! makes to ADR-1571's.
//!
//! Two of those leaves — fuel exhausted, and `Nat.ble cols pc = true` — share
//! one derivation, because `Nat.add` recurses on its right argument and so
//! `Le cols (Nat.add pc 0)` IS `Le cols pc`. Writing H4 as `pc + fuel` rather
//! than `fuel + pc` is what makes that identity definitional.
//!
//! ## Where each prerequisite is spent
//!
//! | branch | what it must re-establish | what pays for it |
//! |---|---|---|
//! | no pivot (`pc` alone advances) | H3 gains column `pc` | `Rat.pivotSearch_column_zero` |
//! | pivot found | H3's old columns | `Rat.rowSwap_preserves_zero_range` then `Rat.clearBelow_preserves_zero` |
//! | pivot found | H3's new column `pc` | `Rat.clearBelow_zero` |
//! | pivot found | H1/H2 over the placed rows | `Rat.clearBelow_rowSwap_off` + `Rat.leadingIndex_congr_row` |
//! | pivot found | the new row leads at exactly `pc` | `Rat.leadingIndex_eq_of_first_nonzero` |
//! | either exit | zero rows read `cols` | `Rat.leadingIndex_eq_cols_of_zero_row` |
//!
//! `Rat.pivotSearch_ge_start` is what makes the pivot branch's two range lemmas
//! applicable at all: both need the found row to be at or below the cursor, and
//! ADR-1558 had only landed the other side of that bound.
//!
//! ## The row-swap lemma, and why its two bounds are hypotheses
//!
//! ```text
//! Rat.rowSwap_preserves_zero_range :
//!   ∀ M pr piv rows k, Le pr piv → Lt piv rows →
//!     (∀ s, Le pr s → Lt s rows → Eq Rat (M s k) Rat.zero) →
//!     ∀ s, Le pr s → Lt s rows → Eq Rat (rowSwap pr piv M s k) Rat.zero
//! ```
//!
//! `rowSwap pr piv M` reads row `piv` into position `pr`, so the conclusion at
//! `s = pr` is a claim about `M piv k` — and the hypothesis only speaks about
//! rows in `[pr, rows)`. Both bounds are load bearing, and the tests exhibit a
//! matrix refuting the statement with each one dropped. `Lt pr rows` is NOT a
//! hypothesis: it follows from the two that are.
//!
//! Its inner split is worse than not free: `Rat.rowSwap_at_right` needs
//! `Nat.beq piv pr = false`, which is the OUTER split's `false` hypothesis
//! transported along `s = piv`. That is why the outer test is `Nat.beq s pr`
//! and not `Nat.beq s piv` — the other way round the inner branch would have to
//! produce that side condition out of nothing.

use super::RatPrelude;
use super::echelon::{
    bool_select_at, rclear_below, ris_zero_b, rleading_index, rpivot_search, rrow_swap,
};
use super::matrix_det::mat_ty;
use super::ops::{nat_rewrite_prop, rat_eq_rewrite, req, rsymm, rtrans, rzero};
use super::rank_bridge::bool_cases;
use crate::KernelError;
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::NatOps;
use crate::nat_prelude::steps::{absurd, or_cases};

/// Declare everything this file builds.
///
/// # Errors
///
/// Returns the trusted gate's rejection — an `Err` means the kernel
/// **refused** a declaration, not that a script gave up.
pub(super) fn declare_echelon_invariant(
    d: &mut IntDev<'_>,
    p: RatPrelude,
) -> Result<(), KernelError> {
    declare_row_swap_preserves_zero_range(d, p)?;
    declare_leading_index_aux_congr_row(d, p)?;
    declare_leading_index_congr_row(d, p)?;
    declare_clear_below_row_swap_off(d, p)?;
    declare_pivot_search_aux_ge_start(d, p)?;
    declare_pivot_search_ge_start(d, p)?;
    declare_is_echelon_aux_of_pairs(d, p)?;
    declare_is_echelon_of_pairs(d, p)?;
    declare_echelon_step_ok_of_lt(d, p)?;
    declare_echelon_step_ok_both_cols(d, p)?;
    declare_echelon_aux_is_echelon(d, p)?;
    declare_row_echelon_is_echelon(d, p)?;
    Ok(())
}

/// Admit `Rat.pivotSearchAux_ge_start : ∀ M c rows fuel r,
/// Lt (pivotSearchAux M c rows fuel r) rows →
/// Le r (pivotSearchAux M c rows fuel r)`.
///
/// *A pivot found IN RANGE is at or below where the search started.*
///
/// The bound on the answer is conditional and it has to be: both exhaustion
/// routes answer `rows`, and `rows` is not `≥ r` when the scan was started past
/// the row count. `Lt … rows` is exactly the hypothesis that rules those out,
/// and it is what `echelonAux`'s pivot branch already has — that branch is
/// taken on `Nat.ble rows piv = false`.
///
/// ADR-1558 landed the OTHER side of this bound (`pivotSearch_le_rows`, which
/// needs no hypothesis because `rows` satisfies it). Together they say the
/// found pivot lives in `[start, rows)`, which is what
/// [`declare_row_swap_preserves_zero_range`] and
/// [`declare_clear_below_row_swap_off`] both demand.
fn declare_pivot_search_aux_ge_start(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let mty = mat_ty(d);

    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let rows_fv = d.fresh_fvar();
    let rows = d.kernel().fvar(rows_fv);

    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        let found = d.const_app(p.pivot_search_aux, &[m, c, rows, x, r]);
        let hyp = NatOps::lt(d, found, rows);
        let concl = NatOps::le(d, r, found);
        let body = d.arrow(hyp, concl);
        d.pi_fv(r_fv, nat, body)
    };

    // Both exhaustion answers are `rows`, so `Lt rows rows` refutes them.
    let refute = |d: &mut IntDev<'_>, r: ExprId| -> ExprId {
        let hyp = NatOps::lt(d, rows, rows);
        let concl = NatOps::le(d, r, rows);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let lt_irrefl = d.prelude().lt_irrefl;
        let contradiction = d.lemma(lt_irrefl, &[rows, h]);
        let inner = absurd(d, concl, contradiction);
        d.lam_fv(h_fv, hyp, inner)
    };

    let base = |d: &mut IntDev<'_>| -> ExprId {
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        let body = refute(d, r);
        d.lam_fv(r_fv, nat, body)
    };

    let step = |d: &mut IntDev<'_>, n: ExprId, ih: ExprId| -> ExprId {
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        let sr = d.succ(r);

        let rec_next = d.const_app(p.pivot_search_aux, &[m, c, rows, n, sr]);
        let entry = d.apply(m, &[r, c]);
        let is_zero = ris_zero_b(d, p, entry);
        let inner_sel = {
            let nat_i = d.nat_ty();
            bool_select_at(d, nat_i, is_zero, rec_next, r)
        };
        let oor = NatOps::ble(d, rows, r);

        let claim = |d: &mut IntDev<'_>, answer: ExprId| -> ExprId {
            let hyp = NatOps::lt(d, answer, rows);
            let concl = NatOps::le(d, r, answer);
            d.arrow(hyp, concl)
        };
        let outer_shape = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
            let nat_i = d.nat_ty();
            let sel = bool_select_at(d, nat_i, x, rows, inner_sel);
            claim(d, sel)
        };
        let inner_shape = |d: &mut IntDev<'_>, y: ExprId| -> ExprId {
            let nat_i = d.nat_ty();
            let sel = bool_select_at(d, nat_i, y, rec_next, r);
            claim(d, sel)
        };

        let goal = outer_shape(d, oor);
        let true_ = d.bool_true();
        let false_ = d.bool_false();
        let h_true_ty = d.bool_eq(oor, true_);
        let h_false_ty = d.bool_eq(oor, false_);

        let stopped = {
            let ht_fv = d.fresh_fvar();
            let ht = d.kernel().fvar(ht_fv);
            let refl_case = refute(d, r);
            let motive_x = d.bool_eq_motive(true_, &outer_shape);
            let ht_sym = d.bool_symm(oor, true_, ht);
            let inner = d.bool_transport(true_, motive_x, refl_case, oor, ht_sym);
            d.lam_fv(ht_fv, h_true_ty, inner)
        };

        let scanning = {
            let hf_fv = d.fresh_fvar();
            let hf = d.kernel().fvar(hf_fv);

            let z_true_ty = d.bool_eq(is_zero, true_);
            let z_false_ty = d.bool_eq(is_zero, false_);
            let inner_goal = inner_shape(d, is_zero);

            // The entry here is zero, so the scan moved on: the answer is one
            // row further down and `Le r` follows from `Le (succ r)`.
            let moved_on = {
                let hz_fv = d.fresh_fvar();
                let hz = d.kernel().fvar(hz_fv);
                let refl_case = {
                    let h_fv = d.fresh_fvar();
                    let h = d.kernel().fvar(h_fv);
                    let hyp = NatOps::lt(d, rec_next, rows);
                    let from_ih = d.apply(ih, &[sr, h]);
                    let le_succ = d.prelude().le_succ;
                    let le_trans = d.prelude().le_trans;
                    let up = d.lemma(le_succ, &[r]);
                    let joined = d.lemma(le_trans, &[r, sr, rec_next, up, from_ih]);
                    d.lam_fv(h_fv, hyp, joined)
                };
                let motive_y = d.bool_eq_motive(true_, &inner_shape);
                let hz_sym = d.bool_symm(is_zero, true_, hz);
                let inner = d.bool_transport(true_, motive_y, refl_case, is_zero, hz_sym);
                d.lam_fv(hz_fv, z_true_ty, inner)
            };

            // The entry here is nonzero: the answer is `r` itself.
            let found_here = {
                let hz_fv = d.fresh_fvar();
                let hz = d.kernel().fvar(hz_fv);
                let refl_case = {
                    let h_fv = d.fresh_fvar();
                    let hyp = NatOps::lt(d, r, rows);
                    let le_refl = d.prelude().le_refl_thm;
                    let body = d.lemma(le_refl, &[r]);
                    d.lam_fv(h_fv, hyp, body)
                };
                let motive_y = d.bool_eq_motive(false_, &inner_shape);
                let hz_sym = d.bool_symm(is_zero, false_, hz);
                let inner = d.bool_transport(false_, motive_y, refl_case, is_zero, hz_sym);
                d.lam_fv(hz_fv, z_false_ty, inner)
            };

            let z_split = bool_cases(d, is_zero);
            let chosen = or_cases(
                d, z_true_ty, z_false_ty, inner_goal, moved_on, found_here, z_split,
            );
            let motive_x = d.bool_eq_motive(false_, &outer_shape);
            let hf_sym = d.bool_symm(oor, false_, hf);
            let inner = d.bool_transport(false_, motive_x, chosen, oor, hf_sym);
            d.lam_fv(hf_fv, h_false_ty, inner)
        };

        let split = bool_cases(d, oor);
        let body = or_cases(d, h_true_ty, h_false_ty, goal, stopped, scanning, split);
        d.lam_fv(r_fv, nat, body)
    };

    let fuel_fv = d.fresh_fvar();
    let fuel = d.kernel().fvar(fuel_fv);
    let proof = d.induct(&motive, &base, &step, fuel);
    let stmt = motive(d, fuel);

    let ty = {
        let over_fuel = d.pi_fv(fuel_fv, nat, stmt);
        let over_rows = d.pi_fv(rows_fv, nat, over_fuel);
        let over_c = d.pi_fv(c_fv, nat, over_rows);
        d.pi_fv(m_fv, mty, over_c)
    };
    let value = {
        let over_fuel = d.lam_fv(fuel_fv, nat, proof);
        let over_rows = d.lam_fv(rows_fv, nat, over_fuel);
        let over_c = d.lam_fv(c_fv, nat, over_rows);
        d.lam_fv(m_fv, mty, over_c)
    };
    d.declare_theorem(p.pivot_search_aux_ge_start, ty, value)
}

/// Admit `Rat.pivotSearch_ge_start : ∀ M c start rows,
/// Lt (pivotSearch M c start rows) rows →
/// Le start (pivotSearch M c start rows)`.
fn declare_pivot_search_ge_start(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let mty = mat_ty(d);

    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let start_fv = d.fresh_fvar();
    let start = d.kernel().fvar(start_fv);
    let rows_fv = d.fresh_fvar();
    let rows = d.kernel().fvar(rows_fv);

    let found = d.const_app(p.pivot_search, &[m, c, start, rows]);
    let hyp_ty = NatOps::lt(d, found, rows);
    let concl = NatOps::le(d, start, found);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let aux = d.lemma(p.pivot_search_aux_ge_start, &[m, c, rows, rows, start]);
    let proof = d.apply(aux, &[h]);

    let ty = {
        let over_h = d.pi_fv(h_fv, hyp_ty, concl);
        let over_rows = d.pi_fv(rows_fv, nat, over_h);
        let over_start = d.pi_fv(start_fv, nat, over_rows);
        let over_c = d.pi_fv(c_fv, nat, over_start);
        d.pi_fv(m_fv, mty, over_c)
    };
    let value = {
        let over_h = d.lam_fv(h_fv, hyp_ty, proof);
        let over_rows = d.lam_fv(rows_fv, nat, over_h);
        let over_start = d.lam_fv(start_fv, nat, over_rows);
        let over_c = d.lam_fv(c_fv, nat, over_start);
        d.lam_fv(m_fv, mty, over_c)
    };
    d.declare_theorem(p.pivot_search_ge_start, ty, value)
}

/// `∀ q, Le lo q → Lt (succ q) rows →
/// Eq Bool (echelonStepOk (leadingIndex M q cols) (leadingIndex M (succ q) cols)
/// cols) true` — every adjacent row pair from `lo` down passes the echelon
/// test.
fn pairs_ok_from(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    m: ExprId,
    rows: ExprId,
    cols: ExprId,
    lo: ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let q_fv = d.fresh_fvar();
    let q = d.kernel().fvar(q_fv);
    let sq = d.succ(q);
    let lower = NatOps::le(d, lo, q);
    let upper = NatOps::lt(d, sq, rows);
    let l1 = rleading_index(d, p, m, q, cols);
    let l2 = rleading_index(d, p, m, sq, cols);
    let ok = d.const_app(p.echelon_step_ok, &[l1, l2, cols]);
    let true_ = d.bool_true();
    let concl = d.bool_eq(ok, true_);
    let inner = d.arrow(upper, concl);
    let body = d.arrow(lower, inner);
    d.pi_fv(q_fv, nat, body)
}

/// Admit `Rat.isEchelonAux_of_pairs : ∀ M rows cols fuel r,
/// (∀ q, Le r q → Lt (succ q) rows →
///   Eq Bool (echelonStepOk (leadingIndex M q cols) (leadingIndex M (succ q)
///   cols) cols) true) →
/// Eq Bool (isEchelonAux M rows cols fuel r) true`.
///
/// *The `Bool` predicate is exactly the adjacent-pair condition*, which is what
/// turns the loop invariant into `isEchelon` at the exit.
///
/// **No fuel bound is needed**, and by ADR-1571 §2's rule that is forced:
/// `isEchelonAux` answers `true` when its fuel runs out, and `true` is the
/// conclusion, so the exhaustion answer satisfies the postcondition directly.
/// The contrast is `Rat.pivotSearchAux_ge_start` above, whose exhaustion answer
/// falsifies its conclusion and which therefore has to refute both exhaustion
/// leaves from a hypothesis.
fn declare_is_echelon_aux_of_pairs(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let mty = mat_ty(d);

    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let rows_fv = d.fresh_fvar();
    let rows = d.kernel().fvar(rows_fv);
    let cols_fv = d.fresh_fvar();
    let cols = d.kernel().fvar(cols_fv);

    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        let hyp = pairs_ok_from(d, p, m, rows, cols, r);
        let scanned = d.const_app(p.is_echelon_aux, &[m, rows, cols, x, r]);
        let true_ = d.bool_true();
        let concl = d.bool_eq(scanned, true_);
        let body = d.arrow(hyp, concl);
        d.pi_fv(r_fv, nat, body)
    };

    let base = |d: &mut IntDev<'_>| -> ExprId {
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        let hyp = pairs_ok_from(d, p, m, rows, cols, r);
        let h_fv = d.fresh_fvar();
        let true_ = d.bool_true();
        let body = d.bool_refl(true_);
        let over_h = d.lam_fv(h_fv, hyp, body);
        d.lam_fv(r_fv, nat, over_h)
    };

    let step = |d: &mut IntDev<'_>, n: ExprId, ih: ExprId| -> ExprId {
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        let hyp_ty = pairs_ok_from(d, p, m, rows, cols, r);
        let hp_fv = d.fresh_fvar();
        let hp = d.kernel().fvar(hp_fv);

        let sr = d.succ(r);
        let l1 = rleading_index(d, p, m, r, cols);
        let l2 = rleading_index(d, p, m, sr, cols);
        let ok = d.const_app(p.echelon_step_ok, &[l1, l2, cols]);
        let rec_next = d.const_app(p.is_echelon_aux, &[m, rows, cols, n, sr]);
        let last_row = NatOps::ble(d, rows, sr);

        let true_ = d.bool_true();
        let false_ = d.bool_false();

        let inner_shape = |d: &mut IntDev<'_>, y: ExprId| -> ExprId {
            let bool_ty = d.bool_ty();
            let false_inner = d.bool_false();
            let sel = bool_select_at(d, bool_ty, y, rec_next, false_inner);
            let true_inner = d.bool_true();
            d.bool_eq(sel, true_inner)
        };
        let outer_shape = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
            let bool_ty = d.bool_ty();
            let inner = {
                let false_inner = d.bool_false();
                bool_select_at(d, bool_ty, ok, rec_next, false_inner)
            };
            let true_inner = d.bool_true();
            let sel = bool_select_at(d, bool_ty, x, true_inner, inner);
            let true_outer = d.bool_true();
            d.bool_eq(sel, true_outer)
        };

        let goal = outer_shape(d, last_row);
        let h_true_ty = d.bool_eq(last_row, true_);
        let h_false_ty = d.bool_eq(last_row, false_);

        // There is no row below `succ r`, so there is no pair left to check.
        let at_the_bottom = {
            let ht_fv = d.fresh_fvar();
            let ht = d.kernel().fvar(ht_fv);
            let refl_case = d.bool_refl(true_);
            let motive_x = d.bool_eq_motive(true_, &outer_shape);
            let ht_sym = d.bool_symm(last_row, true_, ht);
            let inner = d.bool_transport(true_, motive_x, refl_case, last_row, ht_sym);
            d.lam_fv(ht_fv, h_true_ty, inner)
        };

        let keep_scanning = {
            let hf_fv = d.fresh_fvar();
            let hf = d.kernel().fvar(hf_fv);

            let lt_of_ble_eq_false = d.prelude().lt_of_ble_eq_false;
            let sr_lt_rows = d.lemma(lt_of_ble_eq_false, &[rows, sr, hf]);
            let le_refl = d.prelude().le_refl_thm;
            let r_le_r = d.lemma(le_refl, &[r]);
            let this_pair = d.apply(hp, &[r, r_le_r, sr_lt_rows]);

            // The induction hypothesis, with the pair condition restarted one
            // row further down.
            let carried = {
                let q_fv = d.fresh_fvar();
                let q = d.kernel().fvar(q_fv);
                let sq = d.succ(q);
                let lower = NatOps::le(d, sr, q);
                let upper = NatOps::lt(d, sq, rows);
                let hl_fv = d.fresh_fvar();
                let hl = d.kernel().fvar(hl_fv);
                let hu_fv = d.fresh_fvar();
                let hu = d.kernel().fvar(hu_fv);
                let le_succ = d.prelude().le_succ;
                let le_trans = d.prelude().le_trans;
                let up = d.lemma(le_succ, &[r]);
                let r_le_q = d.lemma(le_trans, &[r, sr, q, up, hl]);
                let applied = d.apply(hp, &[q, r_le_q, hu]);
                let with_hu = d.lam_fv(hu_fv, upper, applied);
                let with_hl = d.lam_fv(hl_fv, lower, with_hu);
                d.lam_fv(q_fv, nat, with_hl)
            };
            let from_ih = d.apply(ih, &[sr, carried]);

            let motive_y = d.bool_eq_motive(true_, &inner_shape);
            let pair_sym = d.bool_symm(ok, true_, this_pair);
            let chosen = d.bool_transport(true_, motive_y, from_ih, ok, pair_sym);

            let motive_x = d.bool_eq_motive(false_, &outer_shape);
            let hf_sym = d.bool_symm(last_row, false_, hf);
            let inner = d.bool_transport(false_, motive_x, chosen, last_row, hf_sym);
            d.lam_fv(hf_fv, h_false_ty, inner)
        };

        let split = bool_cases(d, last_row);
        let body = or_cases(
            d,
            h_true_ty,
            h_false_ty,
            goal,
            at_the_bottom,
            keep_scanning,
            split,
        );
        let over_hp = d.lam_fv(hp_fv, hyp_ty, body);
        d.lam_fv(r_fv, nat, over_hp)
    };

    let fuel_fv = d.fresh_fvar();
    let fuel = d.kernel().fvar(fuel_fv);
    let proof = d.induct(&motive, &base, &step, fuel);
    let stmt = motive(d, fuel);

    let ty = {
        let over_fuel = d.pi_fv(fuel_fv, nat, stmt);
        let over_cols = d.pi_fv(cols_fv, nat, over_fuel);
        let over_rows = d.pi_fv(rows_fv, nat, over_cols);
        d.pi_fv(m_fv, mty, over_rows)
    };
    let value = {
        let over_fuel = d.lam_fv(fuel_fv, nat, proof);
        let over_cols = d.lam_fv(cols_fv, nat, over_fuel);
        let over_rows = d.lam_fv(rows_fv, nat, over_cols);
        d.lam_fv(m_fv, mty, over_rows)
    };
    d.declare_theorem(p.is_echelon_aux_of_pairs, ty, value)
}

/// Admit `Rat.isEchelon_of_pairs : ∀ M rows cols,
/// (∀ q, Lt (succ q) rows →
///   Eq Bool (echelonStepOk (leadingIndex M q cols) (leadingIndex M (succ q)
///   cols) cols) true) →
/// Eq Bool (isEchelon M rows cols) true`.
///
/// [`declare_is_echelon_aux_of_pairs`] at the cursor `0`, where `Le 0 q` is
/// `Nat.zero_le` and the caller therefore never has to mention it.
fn declare_is_echelon_of_pairs(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let mty = mat_ty(d);

    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let rows_fv = d.fresh_fvar();
    let rows = d.kernel().fvar(rows_fv);
    let cols_fv = d.fresh_fvar();
    let cols = d.kernel().fvar(cols_fv);

    // `∀ q, Lt (succ q) rows → …` — the same condition with no lower bound.
    let hyp_ty = {
        let q_fv = d.fresh_fvar();
        let q = d.kernel().fvar(q_fv);
        let sq = d.succ(q);
        let upper = NatOps::lt(d, sq, rows);
        let l1 = rleading_index(d, p, m, q, cols);
        let l2 = rleading_index(d, p, m, sq, cols);
        let ok = d.const_app(p.echelon_step_ok, &[l1, l2, cols]);
        let true_ = d.bool_true();
        let concl = d.bool_eq(ok, true_);
        let body = d.arrow(upper, concl);
        d.pi_fv(q_fv, nat, body)
    };
    let hyp_fv = d.fresh_fvar();
    let hyp = d.kernel().fvar(hyp_fv);

    let scanned = d.const_app(p.is_echelon, &[m, rows, cols]);
    let true_ = d.bool_true();
    let concl = d.bool_eq(scanned, true_);

    let zero_n = d.zero();
    let widened = {
        let q_fv = d.fresh_fvar();
        let q = d.kernel().fvar(q_fv);
        let sq = d.succ(q);
        let lower = NatOps::le(d, zero_n, q);
        let upper = NatOps::lt(d, sq, rows);
        let hl_fv = d.fresh_fvar();
        let hu_fv = d.fresh_fvar();
        let hu = d.kernel().fvar(hu_fv);
        let applied = d.apply(hyp, &[q, hu]);
        let with_hu = d.lam_fv(hu_fv, upper, applied);
        let with_hl = d.lam_fv(hl_fv, lower, with_hu);
        d.lam_fv(q_fv, nat, with_hl)
    };
    let aux = d.lemma(p.is_echelon_aux_of_pairs, &[m, rows, cols, rows, zero_n]);
    let proof = d.apply(aux, &[widened]);

    let ty = {
        let over_hyp = d.pi_fv(hyp_fv, hyp_ty, concl);
        let over_cols = d.pi_fv(cols_fv, nat, over_hyp);
        let over_rows = d.pi_fv(rows_fv, nat, over_cols);
        d.pi_fv(m_fv, mty, over_rows)
    };
    let value = {
        let over_hyp = d.lam_fv(hyp_fv, hyp_ty, proof);
        let over_cols = d.lam_fv(cols_fv, nat, over_hyp);
        let over_rows = d.lam_fv(rows_fv, nat, over_cols);
        d.lam_fv(m_fv, mty, over_rows)
    };
    d.declare_theorem(p.is_echelon_of_pairs, ty, value)
}

/// `Not (Eq Nat a b)` from `h : Lt a b`.
///
/// `Nat`'s own copy of this lives in `nat_prelude::finite` and is `pub(super)`
/// there, so it is not reachable from here; it is four lines and re-deriving
/// them is cheaper than widening a `Nat` visibility for one rational consumer.
fn ne_of_lt(d: &mut IntDev<'_>, a: ExprId, b: ExprId, h: ExprId) -> ExprId {
    let eq_ab = d.eq(a, b);
    let e_fv = d.fresh_fvar();
    let e = d.kernel().fvar(e_fv);
    let h_rev = NatOps::symm(d, a, b, e);
    let motive = NatOps::eq_motive(d, b, &|d, x| NatOps::lt(d, a, x));
    let laa = NatOps::transport(d, b, motive, h, a, h_rev);
    let lt_irrefl = d.prelude().lt_irrefl;
    let contra = d.lemma(lt_irrefl, &[a, laa]);
    d.lam_fv(e_fv, eq_ab, contra)
}

/// `Eq Bool (Nat.beq a b) Bool.false` from `h : Lt a b`.
fn beq_false_of_lt(d: &mut IntDev<'_>, a: ExprId, b: ExprId, h: ExprId) -> ExprId {
    let hne = ne_of_lt(d, a, b, h);
    let name = d.prelude().beq_eq_false_of_ne;
    d.lemma(name, &[a, b, hne])
}

/// Admit `Rat.leadingIndexAux_congr_row : ∀ M N r r' cols,
/// (∀ j, Eq Rat (M r j) (N r' j)) → ∀ fuel c,
/// Eq Nat (leadingIndexAux M r cols fuel c) (leadingIndexAux N r' cols fuel c)`.
///
/// *The leading-index scan reads nothing but its own row*, so two matrices
/// agreeing on one row agree on that row's leading index.
///
/// This is what makes the loop invariant's first clause survive a pivot step
/// WITHOUT `funext`. ADR-1555 records that the row form of rank invariance
/// needs `funext` because it must equate two matrices; here nothing is
/// equated — the hypothesis is pointwise and stays pointwise, and it travels
/// OUTSIDE the induction because the scan changes the column, never the row.
///
/// **There is no `Bool` split in this proof.** The obvious route splits on
/// `Nat.ble cols c` and then on `Rat.isZeroB (M r c)` and has to re-derive the
/// second test's value on the other matrix in each branch. Rewriting instead
/// closes it in two transports: one moves the RECURSIVE CALL along the
/// induction hypothesis, the other moves the ENTRY along the row hypothesis,
/// and each leaves the rest of the branch structure untouched because it is
/// literally the same term on both sides.
fn declare_leading_index_aux_congr_row(
    d: &mut IntDev<'_>,
    p: RatPrelude,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let mty = mat_ty(d);

    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let r_fv = d.fresh_fvar();
    let r = d.kernel().fvar(r_fv);
    let r2_fv = d.fresh_fvar();
    let r2 = d.kernel().fvar(r2_fv);
    let cols_fv = d.fresh_fvar();
    let cols = d.kernel().fvar(cols_fv);

    // `∀ j, Eq Rat (M r j) (N r' j)`.
    let hyp_ty = {
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let left = d.apply(m, &[r, j]);
        let right = d.apply(n, &[r2, j]);
        let body = req(d, left, right);
        d.pi_fv(j_fv, nat, body)
    };
    let hyp_fv = d.fresh_fvar();
    let hyp = d.kernel().fvar(hyp_fv);

    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let c_fv = d.fresh_fvar();
        let c = d.kernel().fvar(c_fv);
        let left = d.const_app(p.leading_index_aux, &[m, r, cols, x, c]);
        let right = d.const_app(p.leading_index_aux, &[n, r2, cols, x, c]);
        let body = d.eq(left, right);
        d.pi_fv(c_fv, nat, body)
    };

    // Both scans answer `cols` when the fuel runs out, so the base case is one
    // `Eq.refl` — the give-up answer does not mention the matrix.
    let base = |d: &mut IntDev<'_>| -> ExprId {
        let c_fv = d.fresh_fvar();
        let body = d.refl(cols);
        d.lam_fv(c_fv, nat, body)
    };

    let step = |d: &mut IntDev<'_>, j: ExprId, ih: ExprId| -> ExprId {
        let c_fv = d.fresh_fvar();
        let c = d.kernel().fvar(c_fv);
        let sj = d.succ(j);
        let sc = d.succ(c);

        let lhs = d.const_app(p.leading_index_aux, &[m, r, cols, sj, c]);
        let rhs = d.const_app(p.leading_index_aux, &[n, r2, cols, sj, c]);

        let rec_n = d.const_app(p.leading_index_aux, &[n, r2, cols, j, sc]);
        let entry_m = d.apply(m, &[r, c]);

        // One step of the scan, as a function of the entry it tests and the
        // value it recurses into. Both sides ARE this shape; the two transports
        // below move one argument each.
        let shape = |d: &mut IntDev<'_>, entry: ExprId, tail: ExprId| -> ExprId {
            let nat_inner = d.nat_ty();
            let is_zero = ris_zero_b(d, p, entry);
            let keep = bool_select_at(d, nat_inner, is_zero, tail, c);
            let oor = NatOps::ble(d, cols, c);
            bool_select_at(d, nat_inner, oor, cols, keep)
        };

        // `mid` is the left-hand scan with the RIGHT-hand recursion spliced in.
        let mid = shape(d, entry_m, rec_n);

        // Left leg: move the recursive call along the induction hypothesis.
        let rec_m = d.const_app(p.leading_index_aux, &[m, r, cols, j, sc]);
        let ih_at = d.apply(ih, &[sc]);
        let left_leg = {
            let refl_case = d.refl(lhs);
            nat_rewrite_prop(d, rec_m, rec_n, ih_at, refl_case, &|d, t| {
                let target = shape(d, entry_m, t);
                d.eq(lhs, target)
            })
        };

        // Right leg: move the tested entry along the row hypothesis.
        let entry_n = d.apply(n, &[r2, c]);
        let h_entry = d.apply(hyp, &[c]);
        let right_leg = {
            let refl_proof = d.refl(mid);
            rat_eq_rewrite(d, entry_m, entry_n, h_entry, refl_proof, &|d, t| {
                let target = shape(d, t, rec_n);
                d.eq(mid, target)
            })
        };

        let joined = NatOps::trans(d, lhs, mid, rhs, left_leg, right_leg);
        d.lam_fv(c_fv, nat, joined)
    };

    let fuel_fv = d.fresh_fvar();
    let fuel = d.kernel().fvar(fuel_fv);
    let proof = d.induct(&motive, &base, &step, fuel);
    let stmt = motive(d, fuel);

    let ty = {
        let over_fuel = d.pi_fv(fuel_fv, nat, stmt);
        let over_hyp = d.pi_fv(hyp_fv, hyp_ty, over_fuel);
        let over_cols = d.pi_fv(cols_fv, nat, over_hyp);
        let over_r2 = d.pi_fv(r2_fv, nat, over_cols);
        let over_r = d.pi_fv(r_fv, nat, over_r2);
        let over_n = d.pi_fv(n_fv, mty, over_r);
        d.pi_fv(m_fv, mty, over_n)
    };
    let value = {
        let over_fuel = d.lam_fv(fuel_fv, nat, proof);
        let over_hyp = d.lam_fv(hyp_fv, hyp_ty, over_fuel);
        let over_cols = d.lam_fv(cols_fv, nat, over_hyp);
        let over_r2 = d.lam_fv(r2_fv, nat, over_cols);
        let over_r = d.lam_fv(r_fv, nat, over_r2);
        let over_n = d.lam_fv(n_fv, mty, over_r);
        d.lam_fv(m_fv, mty, over_n)
    };
    d.declare_theorem(p.leading_index_aux_congr_row, ty, value)
}

/// Admit `Rat.leadingIndex_congr_row : ∀ M N r r' cols,
/// (∀ j, Eq Rat (M r j) (N r' j)) →
/// Eq Nat (leadingIndex M r cols) (leadingIndex N r' cols)`.
fn declare_leading_index_congr_row(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let mty = mat_ty(d);

    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let r_fv = d.fresh_fvar();
    let r = d.kernel().fvar(r_fv);
    let r2_fv = d.fresh_fvar();
    let r2 = d.kernel().fvar(r2_fv);
    let cols_fv = d.fresh_fvar();
    let cols = d.kernel().fvar(cols_fv);

    let hyp_ty = {
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let left = d.apply(m, &[r, j]);
        let right = d.apply(n, &[r2, j]);
        let body = req(d, left, right);
        d.pi_fv(j_fv, nat, body)
    };
    let hyp_fv = d.fresh_fvar();
    let hyp = d.kernel().fvar(hyp_fv);

    let left = d.const_app(p.leading_index, &[m, r, cols]);
    let right = d.const_app(p.leading_index, &[n, r2, cols]);
    let concl = d.eq(left, right);

    let zero_n = d.zero();
    let aux = d.lemma(
        p.leading_index_aux_congr_row,
        &[m, n, r, r2, cols, hyp, cols],
    );
    let proof = d.apply(aux, &[zero_n]);

    let ty = {
        let over_hyp = d.pi_fv(hyp_fv, hyp_ty, concl);
        let over_cols = d.pi_fv(cols_fv, nat, over_hyp);
        let over_r2 = d.pi_fv(r2_fv, nat, over_cols);
        let over_r = d.pi_fv(r_fv, nat, over_r2);
        let over_n = d.pi_fv(n_fv, mty, over_r);
        d.pi_fv(m_fv, mty, over_n)
    };
    let value = {
        let over_hyp = d.lam_fv(hyp_fv, hyp_ty, proof);
        let over_cols = d.lam_fv(cols_fv, nat, over_hyp);
        let over_r2 = d.lam_fv(r2_fv, nat, over_cols);
        let over_r = d.lam_fv(r_fv, nat, over_r2);
        let over_n = d.lam_fv(n_fv, mty, over_r);
        d.lam_fv(m_fv, mty, over_n)
    };
    d.declare_theorem(p.leading_index_congr_row, ty, value)
}

/// Admit `Rat.clearBelow_rowSwap_off : ∀ M pr piv pc rows r c, Lt r pr →
/// Le pr piv → Eq Rat (clearBelow (rowSwap pr piv M) pr pc rows r c) (M r c)`.
///
/// *One whole pivot step leaves every row above the cursor exactly as it was.*
/// Composed from `Rat.clearBelow_off` and `Rat.rowSwap_off`; the only content
/// is that `Lt r pr` and `Le pr piv` put `r` strictly below BOTH rows the swap
/// touches, which is what `rowSwap_off`'s two `Nat.beq … = false` side
/// conditions want.
///
/// Together with [`declare_leading_index_congr_row`] this is what carries the
/// invariant's clause about the processed prefix through a step: the rows
/// already placed do not move, so neither do their leading indices.
fn declare_clear_below_row_swap_off(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let mty = mat_ty(d);

    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let pr_fv = d.fresh_fvar();
    let pr = d.kernel().fvar(pr_fv);
    let piv_fv = d.fresh_fvar();
    let piv = d.kernel().fvar(piv_fv);
    let pc_fv = d.fresh_fvar();
    let pc = d.kernel().fvar(pc_fv);
    let rows_fv = d.fresh_fvar();
    let rows = d.kernel().fvar(rows_fv);
    let r_fv = d.fresh_fvar();
    let r = d.kernel().fvar(r_fv);
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);

    let hlt_ty = NatOps::lt(d, r, pr);
    let hle_ty = NatOps::le(d, pr, piv);
    let hlt_fv = d.fresh_fvar();
    let hlt = d.kernel().fvar(hlt_fv);
    let hle_fv = d.fresh_fvar();
    let hle = d.kernel().fvar(hle_fv);

    let swapped = rrow_swap(d, p, pr, piv, m);
    let stepped = d.const_app(p.clear_below, &[swapped, pr, pc, rows]);
    let lhs = d.apply(stepped, &[r, c]);
    let rhs = d.apply(m, &[r, c]);
    let concl = req(d, lhs, rhs);

    // `Le r pr` from `Lt r pr`, i.e. `Le r (succ r)` then `Le (succ r) pr`.
    let le_succ = d.prelude().le_succ;
    let le_trans = d.prelude().le_trans;
    let sr = d.succ(r);
    let up = d.lemma(le_succ, &[r]);
    let r_le_pr = d.lemma(le_trans, &[r, sr, pr, up, hlt]);
    let off_sweep = d.lemma(p.clear_below_off, &[swapped, pr, pc, rows, r, c, r_le_pr]);

    // `Lt r piv` is `Le (succ r) piv`, which is `Lt r pr` composed with
    // `Le pr piv`.
    let r_lt_piv = d.lemma(le_trans, &[sr, pr, piv, hlt, hle]);
    let ne_pr = beq_false_of_lt(d, r, pr, hlt);
    let ne_piv = beq_false_of_lt(d, r, piv, r_lt_piv);
    let off_swap = d.lemma(p.row_swap_off, &[pr, piv, m, r, ne_pr, ne_piv, c]);

    let mid = d.apply(swapped, &[r, c]);
    let proof = rtrans(d, lhs, mid, rhs, off_sweep, off_swap);

    let ty = {
        let f2 = d.pi_fv(hle_fv, hle_ty, concl);
        let f1 = d.pi_fv(hlt_fv, hlt_ty, f2);
        let over_c = d.pi_fv(c_fv, nat, f1);
        let over_r = d.pi_fv(r_fv, nat, over_c);
        let over_rows = d.pi_fv(rows_fv, nat, over_r);
        let over_pc = d.pi_fv(pc_fv, nat, over_rows);
        let over_piv = d.pi_fv(piv_fv, nat, over_pc);
        let over_pr = d.pi_fv(pr_fv, nat, over_piv);
        d.pi_fv(m_fv, mty, over_pr)
    };
    let value = {
        let f2 = d.lam_fv(hle_fv, hle_ty, proof);
        let f1 = d.lam_fv(hlt_fv, hlt_ty, f2);
        let over_c = d.lam_fv(c_fv, nat, f1);
        let over_r = d.lam_fv(r_fv, nat, over_c);
        let over_rows = d.lam_fv(rows_fv, nat, over_r);
        let over_pc = d.lam_fv(pc_fv, nat, over_rows);
        let over_piv = d.lam_fv(piv_fv, nat, over_pc);
        let over_pr = d.lam_fv(pr_fv, nat, over_piv);
        d.lam_fv(m_fv, mty, over_pr)
    };
    d.declare_theorem(p.clear_below_row_swap_off, ty, value)
}

/// `∀ s, Le lo s → Lt s rows → Eq Rat (M s k) Rat.zero` — column `k` is zero at
/// every row from `lo` down.
pub(super) fn column_zero_from(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    m: ExprId,
    lo: ExprId,
    rows: ExprId,
    k: ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let s_fv = d.fresh_fvar();
    let s = d.kernel().fvar(s_fv);
    let lower = NatOps::le(d, lo, s);
    let upper = NatOps::lt(d, s, rows);
    let entry = d.apply(m, &[s, k]);
    let zero_r = rzero(d, p);
    let concl = req(d, entry, zero_r);
    let inner = d.arrow(upper, concl);
    let body = d.arrow(lower, inner);
    d.pi_fv(s_fv, nat, body)
}

/// Admit `Rat.rowSwap_preserves_zero_range : ∀ M pr piv rows k, Le pr piv →
/// Lt piv rows → (∀ s, Le pr s → Lt s rows → Eq Rat (M s k) Rat.zero) →
/// ∀ s, Le pr s → Lt s rows → Eq Rat (rowSwap pr piv M s k) Rat.zero`.
///
/// *A column already zero from the pivot row down survives the pivot swap.*
/// The missing row of ADR-1571 §3's table.
fn declare_row_swap_preserves_zero_range(
    d: &mut IntDev<'_>,
    p: RatPrelude,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let mty = mat_ty(d);

    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let pr_fv = d.fresh_fvar();
    let pr = d.kernel().fvar(pr_fv);
    let piv_fv = d.fresh_fvar();
    let piv = d.kernel().fvar(piv_fv);
    let rows_fv = d.fresh_fvar();
    let rows = d.kernel().fvar(rows_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);

    let hpiv_ty = NatOps::le(d, pr, piv);
    let hlt_ty = NatOps::lt(d, piv, rows);
    let hz_ty = column_zero_from(d, p, m, pr, rows, k);

    let swapped = rrow_swap(d, p, pr, piv, m);
    let concl = column_zero_from(d, p, swapped, pr, rows, k);

    let hpiv_fv = d.fresh_fvar();
    let hpiv = d.kernel().fvar(hpiv_fv);
    let hlt_fv = d.fresh_fvar();
    let hlt = d.kernel().fvar(hlt_fv);
    let hz_fv = d.fresh_fvar();
    let hz = d.kernel().fvar(hz_fv);

    let s_fv = d.fresh_fvar();
    let s = d.kernel().fvar(s_fv);
    let h1_ty = NatOps::le(d, pr, s);
    let h2_ty = NatOps::lt(d, s, rows);
    let h1_fv = d.fresh_fvar();
    let h1 = d.kernel().fvar(h1_fv);
    let h2_fv = d.fresh_fvar();
    let h2 = d.kernel().fvar(h2_fv);

    let zero_r = rzero(d, p);
    let goal = {
        let lhs = d.apply(swapped, &[s, k]);
        req(d, lhs, zero_r)
    };

    let true_ = d.bool_true();
    let false_ = d.bool_false();
    let outer_test = NatOps::beq(d, s, pr);
    let outer_true_ty = d.bool_eq(outer_test, true_);
    let outer_false_ty = d.bool_eq(outer_test, false_);

    // `s = pr`: the swap reads row `piv` into position `pr`, and `piv` is in
    // range by the two hypotheses.
    let on_pivot_row = {
        let hb_fv = d.fresh_fvar();
        let hb = d.kernel().fvar(hb_fv);
        let eq_of_beq = d.prelude().eq_of_beq_eq_true;
        let s_eq_pr = d.lemma(eq_of_beq, &[s, pr, hb]);

        let at_left = d.lemma(p.row_swap_at_left, &[pr, piv, m, k]);
        let piv_zero = d.apply(hz, &[piv, hpiv, hlt]);
        let lhs_pr = d.apply(swapped, &[pr, k]);
        let mid = d.apply(m, &[piv, k]);
        let at_pr = rtrans(d, lhs_pr, mid, zero_r, at_left, piv_zero);

        let back = NatOps::symm(d, s, pr, s_eq_pr);
        let moved = nat_rewrite_prop(d, pr, s, back, at_pr, &|d, t| {
            let inner_swapped = rrow_swap(d, p, pr, piv, m);
            let lhs = d.apply(inner_swapped, &[t, k]);
            let zero_inner = rzero(d, p);
            req(d, lhs, zero_inner)
        });
        d.lam_fv(hb_fv, outer_true_ty, moved)
    };

    let off_pivot_row = {
        let hb1_fv = d.fresh_fvar();
        let hb1 = d.kernel().fvar(hb1_fv);

        let inner_test = NatOps::beq(d, s, piv);
        let inner_true_ty = d.bool_eq(inner_test, true_);
        let inner_false_ty = d.bool_eq(inner_test, false_);

        // `s = piv`: the swap reads row `pr` into position `piv`, and reaching
        // the inner write needs `piv ≠ pr` — the OUTER hypothesis moved along
        // `s = piv`.
        let on_found_row = {
            let hb2_fv = d.fresh_fvar();
            let hb2 = d.kernel().fvar(hb2_fv);
            let eq_of_beq = d.prelude().eq_of_beq_eq_true;
            let s_eq_piv = d.lemma(eq_of_beq, &[s, piv, hb2]);

            let piv_ne_pr = nat_rewrite_prop(d, s, piv, s_eq_piv, hb1, &|d, t| {
                let test = NatOps::beq(d, t, pr);
                let false_inner = d.bool_false();
                d.bool_eq(test, false_inner)
            });
            let at_right = d.lemma(p.row_swap_at_right, &[pr, piv, m, piv_ne_pr, k]);

            let lt_of_le_of_lt = d.prelude().lt_of_le_of_lt;
            let pr_lt_rows = d.lemma(lt_of_le_of_lt, &[pr, piv, rows, hpiv, hlt]);
            let le_refl = d.prelude().le_refl_thm;
            let pr_le_pr = d.lemma(le_refl, &[pr]);
            let pr_zero = d.apply(hz, &[pr, pr_le_pr, pr_lt_rows]);

            let lhs_piv = d.apply(swapped, &[piv, k]);
            let mid = d.apply(m, &[pr, k]);
            let at_piv = rtrans(d, lhs_piv, mid, zero_r, at_right, pr_zero);

            let back = NatOps::symm(d, s, piv, s_eq_piv);
            let moved = nat_rewrite_prop(d, piv, s, back, at_piv, &|d, t| {
                let inner_swapped = rrow_swap(d, p, pr, piv, m);
                let lhs = d.apply(inner_swapped, &[t, k]);
                let zero_inner = rzero(d, p);
                req(d, lhs, zero_inner)
            });
            d.lam_fv(hb2_fv, inner_true_ty, moved)
        };

        // Neither endpoint: the row is untouched.
        let untouched = {
            let hb2_fv = d.fresh_fvar();
            let hb2 = d.kernel().fvar(hb2_fv);
            let off = d.lemma(p.row_swap_off, &[pr, piv, m, s, hb1, hb2, k]);
            let original = d.apply(hz, &[s, h1, h2]);
            let lhs = d.apply(swapped, &[s, k]);
            let mid = d.apply(m, &[s, k]);
            let joined = rtrans(d, lhs, mid, zero_r, off, original);
            d.lam_fv(hb2_fv, inner_false_ty, joined)
        };

        let split = bool_cases(d, inner_test);
        let chosen = or_cases(
            d,
            inner_true_ty,
            inner_false_ty,
            goal,
            on_found_row,
            untouched,
            split,
        );
        d.lam_fv(hb1_fv, outer_false_ty, chosen)
    };

    let outer_split = bool_cases(d, outer_test);
    let body = or_cases(
        d,
        outer_true_ty,
        outer_false_ty,
        goal,
        on_pivot_row,
        off_pivot_row,
        outer_split,
    );

    let over_hyps = {
        let l2 = d.lam_fv(h2_fv, h2_ty, body);
        let l1 = d.lam_fv(h1_fv, h1_ty, l2);
        d.lam_fv(s_fv, nat, l1)
    };

    let ty = {
        let f3 = d.pi_fv(hz_fv, hz_ty, concl);
        let f2 = d.pi_fv(hlt_fv, hlt_ty, f3);
        let f1 = d.pi_fv(hpiv_fv, hpiv_ty, f2);
        let over_k = d.pi_fv(k_fv, nat, f1);
        let over_rows = d.pi_fv(rows_fv, nat, over_k);
        let over_piv = d.pi_fv(piv_fv, nat, over_rows);
        let over_pr = d.pi_fv(pr_fv, nat, over_piv);
        d.pi_fv(m_fv, mty, over_pr)
    };
    let value = {
        let l3 = d.lam_fv(hz_fv, hz_ty, over_hyps);
        let l2 = d.lam_fv(hlt_fv, hlt_ty, l3);
        let l1 = d.lam_fv(hpiv_fv, hpiv_ty, l2);
        let over_k = d.lam_fv(k_fv, nat, l1);
        let over_rows = d.lam_fv(rows_fv, nat, over_k);
        let over_piv = d.lam_fv(piv_fv, nat, over_rows);
        let over_pr = d.lam_fv(pr_fv, nat, over_piv);
        d.lam_fv(m_fv, mty, over_pr)
    };
    d.declare_theorem(p.row_swap_preserves_zero_range, ty, value)
}

// --- the loop invariant, and the exit derivation it feeds -------------------

/// `Eq Bool (bool_select_at Bool cond true true) true` — a `Bool` scrutinee
/// whose two branches are both `Bool.true`.
///
/// The split is unavoidable: `Bool.rec` on a stuck scrutinee does not reduce,
/// so the two branches must be produced separately even though they are the
/// same term.
fn select_true_true(d: &mut IntDev<'_>, cond: ExprId) -> ExprId {
    let true_ = d.bool_true();
    let false_ = d.bool_false();
    let shape = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let bool_ty = d.bool_ty();
        let t = d.bool_true();
        let sel = bool_select_at(d, bool_ty, x, t, t);
        let t2 = d.bool_true();
        d.bool_eq(sel, t2)
    };
    let goal = shape(d, cond);
    let h_true_ty = d.bool_eq(cond, true_);
    let h_false_ty = d.bool_eq(cond, false_);

    let on_true = {
        let ht_fv = d.fresh_fvar();
        let ht = d.kernel().fvar(ht_fv);
        let refl_case = d.bool_refl(true_);
        let motive_x = d.bool_eq_motive(true_, &shape);
        let ht_sym = d.bool_symm(cond, true_, ht);
        let inner = d.bool_transport(true_, motive_x, refl_case, cond, ht_sym);
        d.lam_fv(ht_fv, h_true_ty, inner)
    };
    let on_false = {
        let hf_fv = d.fresh_fvar();
        let hf = d.kernel().fvar(hf_fv);
        let refl_case = d.bool_refl(true_);
        let motive_x = d.bool_eq_motive(false_, &shape);
        let hf_sym = d.bool_symm(cond, false_, hf);
        let inner = d.bool_transport(false_, motive_x, refl_case, cond, hf_sym);
        d.lam_fv(hf_fv, h_false_ty, inner)
    };
    let split = bool_cases(d, cond);
    or_cases(d, h_true_ty, h_false_ty, goal, on_true, on_false, split)
}

/// Admit `Rat.echelonStepOk_of_lt : ∀ l1 l2 cols, Lt l1 l2 →
/// Eq Bool (echelonStepOk l1 l2 cols) true`.
///
/// The FIRST disjunct of the test, as a lemma: a leading entry that moved
/// strictly right passes, whatever the column count is.
fn declare_echelon_step_ok_of_lt(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();

    let l1_fv = d.fresh_fvar();
    let l1 = d.kernel().fvar(l1_fv);
    let l2_fv = d.fresh_fvar();
    let l2 = d.kernel().fvar(l2_fv);
    let cols_fv = d.fresh_fvar();
    let cols = d.kernel().fvar(cols_fv);

    let hyp_ty = NatOps::lt(d, l1, l2);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let ok = d.const_app(p.echelon_step_ok, &[l1, l2, cols]);
    let true_ = d.bool_true();
    let concl = d.bool_eq(ok, true_);

    let sl1 = d.succ(l1);
    let strict = NatOps::ble(d, sl1, l2);
    let ble_true = d.prelude().ble_eq_true_of_le;
    let strict_true = d.lemma(ble_true, &[sl1, l2, h]);

    let shape = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let bool_ty = d.bool_ty();
        let first_zero = NatOps::ble(d, cols, l1);
        let second_zero = NatOps::ble(d, cols, l2);
        let false_v = d.bool_false();
        let both_zero = bool_select_at(d, bool_ty, first_zero, second_zero, false_v);
        let true_v = d.bool_true();
        let sel = bool_select_at(d, bool_ty, x, true_v, both_zero);
        let true_out = d.bool_true();
        d.bool_eq(sel, true_out)
    };
    let refl_case = d.bool_refl(true_);
    let motive_x = d.bool_eq_motive(true_, &shape);
    let sym = d.bool_symm(strict, true_, strict_true);
    let proof = d.bool_transport(true_, motive_x, refl_case, strict, sym);

    let ty = {
        let over_h = d.pi_fv(h_fv, hyp_ty, concl);
        let over_cols = d.pi_fv(cols_fv, nat, over_h);
        let over_l2 = d.pi_fv(l2_fv, nat, over_cols);
        d.pi_fv(l1_fv, nat, over_l2)
    };
    let value = {
        let over_h = d.lam_fv(h_fv, hyp_ty, proof);
        let over_cols = d.lam_fv(cols_fv, nat, over_h);
        let over_l2 = d.lam_fv(l2_fv, nat, over_cols);
        d.lam_fv(l1_fv, nat, over_l2)
    };
    d.declare_theorem(p.echelon_step_ok_of_lt, ty, value)
}

/// Admit `Rat.echelonStepOk_both_cols : ∀ cols,
/// Eq Bool (echelonStepOk cols cols cols) true`.
///
/// The SECOND disjunct, at the only pair of values that can satisfy it: a
/// leading index is at most `cols`, so `Nat.ble cols l` says `l = cols`, and
/// two zero rows in a row is the one case the strict clause cannot cover.
/// ADR-1554 records that the second disjunct needs BOTH conjuncts, and this is
/// where they are both spent.
fn declare_echelon_step_ok_both_cols(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();

    let cols_fv = d.fresh_fvar();
    let cols = d.kernel().fvar(cols_fv);

    let ok = d.const_app(p.echelon_step_ok, &[cols, cols, cols]);
    let true_ = d.bool_true();
    let concl = d.bool_eq(ok, true_);

    let bcc = NatOps::ble(d, cols, cols);
    let le_refl = d.prelude().le_refl_thm;
    let cols_le_cols = d.lemma(le_refl, &[cols]);
    let ble_true = d.prelude().ble_eq_true_of_le;
    let bcc_true = d.lemma(ble_true, &[cols, cols, cols_le_cols]);

    // Both `ble cols l1` and `ble cols l2` are the SAME term here, so one
    // motive moves them together.
    let shape = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let bool_ty = d.bool_ty();
        let false_v = d.bool_false();
        let both_zero = bool_select_at(d, bool_ty, x, x, false_v);
        let scols = d.succ(cols);
        let strict = NatOps::ble(d, scols, cols);
        let true_v = d.bool_true();
        let sel = bool_select_at(d, bool_ty, strict, true_v, both_zero);
        let true_out = d.bool_true();
        d.bool_eq(sel, true_out)
    };
    let refl_case = {
        let scols = d.succ(cols);
        let strict = NatOps::ble(d, scols, cols);
        select_true_true(d, strict)
    };
    let motive_x = d.bool_eq_motive(true_, &shape);
    let sym = d.bool_symm(bcc, true_, bcc_true);
    let proof = d.bool_transport(true_, motive_x, refl_case, bcc, sym);

    let ty = d.pi_fv(cols_fv, nat, concl);
    let value = d.lam_fv(cols_fv, nat, proof);
    d.declare_theorem(p.echelon_step_ok_both_cols, ty, value)
}

/// The five clauses of `echelonAux`'s loop invariant, as hypothesis TYPES.
///
/// **They are built here rather than declared as a `Prop`.** ADR-1562 §2's rule
/// applies: a named `Definition` could be well-typed and mean something else,
/// and the reader would have to unfold it to find out. A Rust builder gives the
/// same one-place-to-read as a named predicate while every theorem's type still
/// carries the clauses literally.
///
/// ```text
/// H0 : Le pc cols                                    -- the column cursor is in range
/// H1 : ∀ r, Lt (succ r) pr →                         -- the placed rows already pass the test
///        echelonStepOk (leadingIndex M r cols) (leadingIndex M (succ r) cols) cols = true
/// H2 : ∀ r, Lt r pr → Lt (leadingIndex M r cols) pc  -- ... and all lead LEFT of the cursor
/// H3 : ∀ s c, Le pr s → Lt s rows → Lt c pc →        -- everything below is zero left of it
///        Eq Rat (M s c) Rat.zero
/// H4 : Le cols (Nat.add pc fuel)                     -- there is fuel enough to reach `cols`
/// ```
///
/// H0 is not redundant given H4. H4 bounds `pc` from BELOW (via the fuel) and
/// H0 from above, and the exit branch needs the upper bound: it reads
/// `Lt (leadingIndex M r cols) pc` off H2 and has to turn it into
/// `Lt … cols`, which is false without `Le pc cols`.
fn invariant_hyps(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    rows: ExprId,
    cols: ExprId,
    m: ExprId,
    pr: ExprId,
    pc: ExprId,
    fuel: ExprId,
) -> [ExprId; 5] {
    let nat = d.nat_ty();

    let h0 = NatOps::le(d, pc, cols);

    let h1 = {
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        let sr = d.succ(r);
        let bound = NatOps::lt(d, sr, pr);
        let l1 = rleading_index(d, p, m, r, cols);
        let l2 = rleading_index(d, p, m, sr, cols);
        let ok = d.const_app(p.echelon_step_ok, &[l1, l2, cols]);
        let true_ = d.bool_true();
        let concl = d.bool_eq(ok, true_);
        let body = d.arrow(bound, concl);
        d.pi_fv(r_fv, nat, body)
    };

    let h2 = {
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        let bound = NatOps::lt(d, r, pr);
        let l = rleading_index(d, p, m, r, cols);
        let concl = NatOps::lt(d, l, pc);
        let body = d.arrow(bound, concl);
        d.pi_fv(r_fv, nat, body)
    };

    let h3 = {
        let s_fv = d.fresh_fvar();
        let s = d.kernel().fvar(s_fv);
        let c_fv = d.fresh_fvar();
        let c = d.kernel().fvar(c_fv);
        let lower = NatOps::le(d, pr, s);
        let upper = NatOps::lt(d, s, rows);
        let left = NatOps::lt(d, c, pc);
        let entry = d.apply(m, &[s, c]);
        let zero_r = rzero(d, p);
        let concl = req(d, entry, zero_r);
        let after_left = d.arrow(left, concl);
        let after_upper = d.arrow(upper, after_left);
        let after_lower = d.arrow(lower, after_upper);
        let over_c = d.pi_fv(c_fv, nat, after_lower);
        d.pi_fv(s_fv, nat, over_c)
    };

    let h4 = {
        let sum = NatOps::add(d, pc, fuel);
        NatOps::le(d, cols, sum)
    };

    [h0, h1, h2, h3, h4]
}

/// `Eq Bool (isEchelon M rows cols) true` when the ROW cursor has reached the
/// row count: every adjacent pair in range is a pair the invariant already
/// checked.
fn exit_rows_done(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    m: ExprId,
    rows: ExprId,
    cols: ExprId,
    pr: ExprId,
    h1: ExprId,
    rows_le_pr: ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let q_fv = d.fresh_fvar();
    let q = d.kernel().fvar(q_fv);
    let sq = d.succ(q);
    let upper = NatOps::lt(d, sq, rows);
    let hu_fv = d.fresh_fvar();
    let hu = d.kernel().fvar(hu_fv);

    let lt_of_lt_of_le = d.prelude().lt_of_lt_of_le;
    let in_prefix = d.lemma(lt_of_lt_of_le, &[sq, rows, pr, hu, rows_le_pr]);
    let applied = d.apply(h1, &[q, in_prefix]);
    let with_hu = d.lam_fv(hu_fv, upper, applied);
    let pairs = d.lam_fv(q_fv, nat, with_hu);

    let thm = d.lemma(p.is_echelon_of_pairs, &[m, rows, cols]);
    d.apply(thm, &[pairs])
}

/// `Eq Bool (isEchelon M rows cols) true` when the COLUMN cursor has reached
/// the column count.
///
/// This is the branch that spends every clause of the invariant at once, and it
/// is a three-way split on where the pair sits relative to the row cursor:
/// entirely in the placed prefix (H1 verbatim), entirely below it (both rows
/// are zero throughout, so both leading indices are `cols` and the SECOND
/// disjunct of `echelonStepOk` fires), or straddling it (the last placed row
/// leads strictly left of `cols`, so the FIRST disjunct fires).
#[allow(clippy::too_many_arguments)]
fn exit_cols_done(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    m: ExprId,
    rows: ExprId,
    cols: ExprId,
    pr: ExprId,
    pc: ExprId,
    hs: [ExprId; 5],
    cols_le_pc: ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let [h0, h1, h2, h3, _h4] = hs;

    // A row at or below the cursor is zero across the whole width, so its
    // leading index is `cols`.
    let zero_row = |d: &mut IntDev<'_>, s: ExprId, ge: ExprId, lt: ExprId| -> ExprId {
        let nat_i = d.nat_ty();
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let bound = NatOps::lt(d, k, cols);
        let hk_fv = d.fresh_fvar();
        let hk = d.kernel().fvar(hk_fv);
        let lt_of_lt_of_le = d.prelude().lt_of_lt_of_le;
        let k_lt_pc = d.lemma(lt_of_lt_of_le, &[k, cols, pc, hk, cols_le_pc]);
        let z = d.apply(h3, &[s, k, ge, lt, k_lt_pc]);
        let with_hk = d.lam_fv(hk_fv, bound, z);
        let f = d.lam_fv(k_fv, nat_i, with_hk);
        d.lemma(p.leading_index_eq_cols_of_zero_row, &[m, s, cols, f])
    };

    let q_fv = d.fresh_fvar();
    let q = d.kernel().fvar(q_fv);
    let sq = d.succ(q);
    let ssq = d.succ(sq);
    let upper = NatOps::lt(d, sq, rows);
    let hu_fv = d.fresh_fvar();
    let hu = d.kernel().fvar(hu_fv);

    let l1v = rleading_index(d, p, m, q, cols);
    let l2v = rleading_index(d, p, m, sq, cols);
    let goal = {
        let ok = d.const_app(p.echelon_step_ok, &[l1v, l2v, cols]);
        let true_ = d.bool_true();
        d.bool_eq(ok, true_)
    };

    let left_ty = NatOps::lt(d, sq, pr);
    let right_ty = NatOps::le(d, pr, sq);

    let in_prefix = {
        let hl_fv = d.fresh_fvar();
        let hl = d.kernel().fvar(hl_fv);
        let applied = d.apply(h1, &[q, hl]);
        d.lam_fv(hl_fv, left_ty, applied)
    };

    let at_or_below = {
        let hr_fv = d.fresh_fvar();
        let hr = d.kernel().fvar(hr_fv);

        let lt_or_eq_of_le = d.prelude().lt_or_eq_of_le;
        let split2 = d.lemma(lt_or_eq_of_le, &[pr, sq, hr]);
        let strict_ty = NatOps::lt(d, pr, sq);
        let eq_ty = d.eq(pr, sq);

        // Both rows sit at or below the cursor: both are zero rows.
        let both_below = {
            let hlt_fv = d.fresh_fvar();
            let hlt = d.kernel().fvar(hlt_fv);
            let le_of_succ_le_succ = d.prelude().le_of_succ_le_succ;
            let pr_le_q = d.lemma(le_of_succ_le_succ, &[pr, q, hlt]);
            let le_succ = d.prelude().le_succ;
            let le_trans = d.prelude().le_trans;
            let up = d.lemma(le_succ, &[sq]);
            let q_lt_rows = d.lemma(le_trans, &[sq, ssq, rows, up, hu]);

            let e1 = zero_row(d, q, pr_le_q, q_lt_rows);
            let e2 = zero_row(d, sq, hr, hu);
            let base = d.lemma(p.echelon_step_ok_both_cols, &[cols]);

            let e2_sym = NatOps::symm(d, l2v, cols, e2);
            let mid = nat_rewrite_prop(d, cols, l2v, e2_sym, base, &|d, t| {
                let ok = d.const_app(p.echelon_step_ok, &[cols, t, cols]);
                let true_ = d.bool_true();
                d.bool_eq(ok, true_)
            });
            let e1_sym = NatOps::symm(d, l1v, cols, e1);
            let moved = nat_rewrite_prop(d, cols, l1v, e1_sym, mid, &|d, t| {
                let right = rleading_index(d, p, m, sq, cols);
                let ok = d.const_app(p.echelon_step_ok, &[t, right, cols]);
                let true_ = d.bool_true();
                d.bool_eq(ok, true_)
            });
            d.lam_fv(hlt_fv, strict_ty, moved)
        };

        // The pair straddles the cursor: the upper row is the last placed one.
        let straddling = {
            let he_fv = d.fresh_fvar();
            let he = d.kernel().fvar(he_fv);

            let lt_succ_self = d.prelude().lt_succ_self;
            let q_lt_sq = d.lemma(lt_succ_self, &[q]);
            let he_sym = NatOps::symm(d, pr, sq, he);
            let q_lt_pr = nat_rewrite_prop(d, sq, pr, he_sym, q_lt_sq, &|d, t| NatOps::lt(d, q, t));

            let h2q = d.apply(h2, &[q, q_lt_pr]);
            let lt_of_lt_of_le = d.prelude().lt_of_lt_of_le;
            let l1_lt_cols = d.lemma(lt_of_lt_of_le, &[l1v, pc, cols, h2q, h0]);
            let base = d.lemma(p.echelon_step_ok_of_lt, &[l1v, cols, cols, l1_lt_cols]);

            let e2 = zero_row(d, sq, hr, hu);
            let e2_sym = NatOps::symm(d, l2v, cols, e2);
            let moved = nat_rewrite_prop(d, cols, l2v, e2_sym, base, &|d, t| {
                let left = rleading_index(d, p, m, q, cols);
                let ok = d.const_app(p.echelon_step_ok, &[left, t, cols]);
                let true_ = d.bool_true();
                d.bool_eq(ok, true_)
            });
            d.lam_fv(he_fv, eq_ty, moved)
        };

        let chosen = or_cases(d, strict_ty, eq_ty, goal, both_below, straddling, split2);
        d.lam_fv(hr_fv, right_ty, chosen)
    };

    let lt_or_ge = d.prelude().lt_or_ge;
    let split = d.lemma(lt_or_ge, &[sq, pr]);
    let body = or_cases(d, left_ty, right_ty, goal, in_prefix, at_or_below, split);
    let with_hu = d.lam_fv(hu_fv, upper, body);
    let pairs = d.lam_fv(q_fv, nat, with_hu);
    let thm = d.lemma(p.is_echelon_of_pairs, &[m, rows, cols]);
    d.apply(thm, &[pairs])
}

/// Admit `Rat.echelonAux_isEchelon : ∀ rows cols fuel M pr pc,
/// (the five invariant clauses) →
/// Eq Bool (isEchelon (echelonAux rows cols fuel M pr pc) rows cols) true`.
///
/// **ADR-1554's obligation 4.** The exit derivation is folded INTO the
/// induction rather than run after it: the conclusion at every fuel level is
/// already the answer, so the three leaves that stop the loop each discharge it
/// from the invariant and nothing has to name the final cursors. ADR-1571 §3
/// sized this as an invariant plus two inductions; carrying the conclusion
/// makes it one.
///
/// The two loop branches are where the four prerequisites are spent, one each:
///
/// - the NO-PIVOT branch advances `pc` alone and extends clause H3 by one
///   column, from `Rat.pivotSearch_column_zero`;
/// - the PIVOT branch swaps and sweeps, and needs
///   `Rat.rowSwap_preserves_zero_range` then `Rat.clearBelow_preserves_zero`
///   for H3's old columns, `Rat.clearBelow_zero` for its new one,
///   `Rat.leadingIndex_eq_of_first_nonzero` to place the new pivot row's
///   leading index at exactly `pc`, and
///   `Rat.clearBelow_rowSwap_off` + `Rat.leadingIndex_congr_row` to carry H1
///   and H2 over the rows already placed.
///
/// `Rat.pivotSearch_ge_start` is what makes the pivot branch's two range
/// lemmas applicable at all: they both need the found row to be at or below the
/// cursor.
#[allow(clippy::too_many_lines)]
fn declare_echelon_aux_is_echelon(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let mty = mat_ty(d);

    let rows_fv = d.fresh_fvar();
    let rows = d.kernel().fvar(rows_fv);
    let cols_fv = d.fresh_fvar();
    let cols = d.kernel().fvar(cols_fv);

    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let pr_fv = d.fresh_fvar();
        let pr = d.kernel().fvar(pr_fv);
        let pc_fv = d.fresh_fvar();
        let pc = d.kernel().fvar(pc_fv);

        let hyps = invariant_hyps(d, p, rows, cols, m, pr, pc, x);
        let answer = d.const_app(p.echelon_aux, &[rows, cols, x, m, pr, pc]);
        let scanned = d.const_app(p.is_echelon, &[answer, rows, cols]);
        let true_ = d.bool_true();
        let concl = d.bool_eq(scanned, true_);

        let mut body = concl;
        for ty in hyps.into_iter().rev() {
            body = d.arrow(ty, body);
        }
        let over_pc = d.pi_fv(pc_fv, nat, body);
        let over_pr = d.pi_fv(pr_fv, nat, over_pc);
        d.pi_fv(m_fv, mty, over_pr)
    };

    // Bind `M`, `pr`, `pc` and the five clauses, then hand them to `body`.
    let bind_all =
        |d: &mut IntDev<'_>,
         fuel: ExprId,
         body: &dyn Fn(&mut IntDev<'_>, ExprId, ExprId, ExprId, [ExprId; 5]) -> ExprId|
         -> ExprId {
            let nat_i = d.nat_ty();
            let mty_i = mat_ty(d);
            let m_fv = d.fresh_fvar();
            let m = d.kernel().fvar(m_fv);
            let pr_fv = d.fresh_fvar();
            let pr = d.kernel().fvar(pr_fv);
            let pc_fv = d.fresh_fvar();
            let pc = d.kernel().fvar(pc_fv);

            let tys = invariant_hyps(d, p, rows, cols, m, pr, pc, fuel);
            let mut fvs = [d.fresh_fvar(); 5];
            for slot in &mut fvs {
                *slot = d.fresh_fvar();
            }
            let mut vals = [m; 5];
            for (slot, fv) in vals.iter_mut().zip(fvs) {
                *slot = d.kernel().fvar(fv);
            }
            let mut inner = body(d, m, pr, pc, vals);
            for i in (0..5).rev() {
                inner = d.lam_fv(fvs[i], tys[i], inner);
            }
            let over_pc = d.lam_fv(pc_fv, nat_i, inner);
            let over_pr = d.lam_fv(pr_fv, nat_i, over_pc);
            d.lam_fv(m_fv, mty_i, over_pr)
        };

    let zero_n = d.zero();
    let base = |d: &mut IntDev<'_>| -> ExprId {
        bind_all(d, zero_n, &|d, m, pr, pc, hs| {
            // `Le cols (Nat.add pc 0)` IS `Le cols pc`: `Nat.add` recurses on
            // its right argument, so the fuel clause degenerates to exactly
            // the column-exhausted condition and the base case and the
            // `cols_done` branch share one derivation.
            exit_cols_done(d, p, m, rows, cols, pr, pc, hs, hs[4])
        })
    };

    let step = |d: &mut IntDev<'_>, n: ExprId, ih: ExprId| -> ExprId {
        let sn = d.succ(n);
        bind_all(d, sn, &|d, m, pr, pc, hs| {
            let mty_i = mat_ty(d);
            let spr = d.succ(pr);
            let spc = d.succ(pc);
            let piv = rpivot_search(d, p, m, pc, pr, rows);
            let swapped = rrow_swap(d, p, pr, piv, m);
            let cleared = rclear_below(d, p, swapped, pr, pc, rows);
            let advance_column = d.const_app(p.echelon_aux, &[rows, cols, n, m, pr, spc]);
            let advance_both = d.const_app(p.echelon_aux, &[rows, cols, n, cleared, spr, spc]);

            let no_pivot = NatOps::ble(d, rows, piv);
            let cols_done = NatOps::ble(d, cols, pc);
            let rows_done = NatOps::ble(d, rows, pr);

            let concl_of = |d: &mut IntDev<'_>, answer: ExprId| -> ExprId {
                let scanned = d.const_app(p.is_echelon, &[answer, rows, cols]);
                let true_ = d.bool_true();
                d.bool_eq(scanned, true_)
            };
            let pivot_shape = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
                let sel = bool_select_at(d, mty_i, x, advance_column, advance_both);
                concl_of(d, sel)
            };
            let cols_shape = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
                let inner = bool_select_at(d, mty_i, no_pivot, advance_column, advance_both);
                let sel = bool_select_at(d, mty_i, x, m, inner);
                concl_of(d, sel)
            };
            let rows_shape = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
                let step_sel = bool_select_at(d, mty_i, no_pivot, advance_column, advance_both);
                let after_cols = bool_select_at(d, mty_i, cols_done, m, step_sel);
                let sel = bool_select_at(d, mty_i, x, m, after_cols);
                concl_of(d, sel)
            };

            let true_ = d.bool_true();
            let false_ = d.bool_false();
            let goal = rows_shape(d, rows_done);
            let rows_true_ty = d.bool_eq(rows_done, true_);
            let rows_false_ty = d.bool_eq(rows_done, false_);

            let stop_on_rows = {
                let ht_fv = d.fresh_fvar();
                let ht = d.kernel().fvar(ht_fv);
                let le_of_ble = d.prelude().le_of_ble_eq_true;
                let rows_le_pr = d.lemma(le_of_ble, &[rows, pr, ht]);
                let refl_case = exit_rows_done(d, p, m, rows, cols, pr, hs[1], rows_le_pr);
                let motive_x = d.bool_eq_motive(true_, &rows_shape);
                let ht_sym = d.bool_symm(rows_done, true_, ht);
                let inner = d.bool_transport(true_, motive_x, refl_case, rows_done, ht_sym);
                d.lam_fv(ht_fv, rows_true_ty, inner)
            };

            let rows_left = {
                let hrf_fv = d.fresh_fvar();
                let hrf = d.kernel().fvar(hrf_fv);

                let cols_goal = cols_shape(d, cols_done);
                let cols_true_ty = d.bool_eq(cols_done, true_);
                let cols_false_ty = d.bool_eq(cols_done, false_);

                let stop_on_cols = {
                    let ht_fv = d.fresh_fvar();
                    let ht = d.kernel().fvar(ht_fv);
                    let le_of_ble = d.prelude().le_of_ble_eq_true;
                    let cols_le_pc = d.lemma(le_of_ble, &[cols, pc, ht]);
                    let refl_case = exit_cols_done(d, p, m, rows, cols, pr, pc, hs, cols_le_pc);
                    let motive_x = d.bool_eq_motive(true_, &cols_shape);
                    let ht_sym = d.bool_symm(cols_done, true_, ht);
                    let inner = d.bool_transport(true_, motive_x, refl_case, cols_done, ht_sym);
                    d.lam_fv(ht_fv, cols_true_ty, inner)
                };

                let keep_going = {
                    let hcf_fv = d.fresh_fvar();
                    let hcf = d.kernel().fvar(hcf_fv);

                    // `Lt pc cols` IS `Le (succ pc) cols`, so this one term is
                    // both the branch condition and the next H0.
                    let lt_of_ble_false = d.prelude().lt_of_ble_eq_false;
                    let pc_lt_cols = d.lemma(lt_of_ble_false, &[cols, pc, hcf]);

                    // The fuel clause, moved from `pc + succ n` to
                    // `succ pc + n`. The first is definitionally
                    // `succ (pc + n)`; the second needs `Nat.succ_add`.
                    let next_fuel = {
                        let add_pc_n = NatOps::add(d, pc, n);
                        let s_add = d.succ(add_pc_n);
                        let add_spc_n = NatOps::add(d, spc, n);
                        let succ_add = d.prelude().succ_add;
                        let sa = d.lemma(succ_add, &[pc, n]);
                        let sa_sym = NatOps::symm(d, add_spc_n, s_add, sa);
                        nat_rewrite_prop(d, s_add, add_spc_n, sa_sym, hs[4], &|d, t| {
                            NatOps::le(d, cols, t)
                        })
                    };

                    let pivot_goal = pivot_shape(d, no_pivot);
                    let pivot_true_ty = d.bool_eq(no_pivot, true_);
                    let pivot_false_ty = d.bool_eq(no_pivot, false_);

                    let column_is_clear = {
                        let ht_fv = d.fresh_fvar();
                        let ht = d.kernel().fvar(ht_fv);

                        let le_of_ble = d.prelude().le_of_ble_eq_true;
                        let rows_le_piv = d.lemma(le_of_ble, &[rows, piv, ht]);
                        let piv_le_rows = d.lemma(p.pivot_search_le_rows, &[m, pc, pr, rows]);
                        let le_antisymm = d.prelude().le_antisymm;
                        let exhausted =
                            d.lemma(le_antisymm, &[piv, rows, piv_le_rows, rows_le_piv]);

                        // H2 widens by one column for free.
                        let next_h2 = {
                            let nat_j = d.nat_ty();
                            let r_fv = d.fresh_fvar();
                            let r = d.kernel().fvar(r_fv);
                            let bound = NatOps::lt(d, r, pr);
                            let hr_fv = d.fresh_fvar();
                            let hr = d.kernel().fvar(hr_fv);
                            let l = rleading_index(d, p, m, r, cols);
                            let sl = d.succ(l);
                            let inner = d.apply(hs[2], &[r, hr]);
                            let le_succ = d.prelude().le_succ;
                            let le_trans = d.prelude().le_trans;
                            let up = d.lemma(le_succ, &[pc]);
                            let widened = d.lemma(le_trans, &[sl, pc, spc, inner, up]);
                            let with_hr = d.lam_fv(hr_fv, bound, widened);
                            d.lam_fv(r_fv, nat_j, with_hr)
                        };

                        // H3 gains column `pc`, which is the ONLY thing the
                        // no-pivot branch establishes.
                        let next_h3 = {
                            let nat_j = d.nat_ty();
                            let s_fv = d.fresh_fvar();
                            let s = d.kernel().fvar(s_fv);
                            let c_fv = d.fresh_fvar();
                            let c = d.kernel().fvar(c_fv);
                            let lower = NatOps::le(d, pr, s);
                            let upper = NatOps::lt(d, s, rows);
                            let left = NatOps::lt(d, c, spc);
                            let hl_fv = d.fresh_fvar();
                            let hl = d.kernel().fvar(hl_fv);
                            let hu_fv = d.fresh_fvar();
                            let hu = d.kernel().fvar(hu_fv);
                            let hc_fv = d.fresh_fvar();
                            let hc = d.kernel().fvar(hc_fv);

                            let entry = d.apply(m, &[s, c]);
                            let zero_r = rzero(d, p);
                            let target = req(d, entry, zero_r);

                            let le_of_succ_le_succ = d.prelude().le_of_succ_le_succ;
                            let c_le_pc = d.lemma(le_of_succ_le_succ, &[c, pc, hc]);
                            let lt_or_eq_of_le = d.prelude().lt_or_eq_of_le;
                            let split = d.lemma(lt_or_eq_of_le, &[c, pc, c_le_pc]);
                            let lt_ty = NatOps::lt(d, c, pc);
                            let eq_ty = d.eq(c, pc);

                            let older = {
                                let hx_fv = d.fresh_fvar();
                                let hx = d.kernel().fvar(hx_fv);
                                let applied = d.apply(hs[3], &[s, c, hl, hu, hx]);
                                d.lam_fv(hx_fv, lt_ty, applied)
                            };
                            let brand_new = {
                                let he_fv = d.fresh_fvar();
                                let he = d.kernel().fvar(he_fv);
                                let at_pc = d.lemma(
                                    p.pivot_search_column_zero,
                                    &[m, pc, pr, rows, s, hl, hu, exhausted],
                                );
                                let he_sym = NatOps::symm(d, c, pc, he);
                                let moved = nat_rewrite_prop(d, pc, c, he_sym, at_pc, &|d, t| {
                                    let e = d.apply(m, &[s, t]);
                                    let z = rzero(d, p);
                                    req(d, e, z)
                                });
                                d.lam_fv(he_fv, eq_ty, moved)
                            };
                            let chosen = or_cases(d, lt_ty, eq_ty, target, older, brand_new, split);
                            let with_hc = d.lam_fv(hc_fv, left, chosen);
                            let with_hu = d.lam_fv(hu_fv, upper, with_hc);
                            let with_hl = d.lam_fv(hl_fv, lower, with_hu);
                            let over_c = d.lam_fv(c_fv, nat_j, with_hl);
                            d.lam_fv(s_fv, nat_j, over_c)
                        };

                        let recursed = d.apply(
                            ih,
                            &[m, pr, spc, pc_lt_cols, hs[1], next_h2, next_h3, next_fuel],
                        );
                        let motive_x = d.bool_eq_motive(true_, &pivot_shape);
                        let ht_sym = d.bool_symm(no_pivot, true_, ht);
                        let inner = d.bool_transport(true_, motive_x, recursed, no_pivot, ht_sym);
                        d.lam_fv(ht_fv, pivot_true_ty, inner)
                    };

                    let pivot_found = {
                        let hf_fv = d.fresh_fvar();
                        let hf = d.kernel().fvar(hf_fv);

                        let lt_of_ble_false2 = d.prelude().lt_of_ble_eq_false;
                        let piv_lt_rows = d.lemma(lt_of_ble_false2, &[rows, piv, hf]);
                        let pr_le_piv =
                            d.lemma(p.pivot_search_ge_start, &[m, pc, pr, rows, piv_lt_rows]);
                        let piv_entry_ne =
                            d.lemma(p.pivot_search_ne_zero, &[m, pc, pr, rows, piv_lt_rows]);

                        let zero_r = rzero(d, p);
                        let at_left_pc = d.lemma(p.row_swap_at_left, &[pr, piv, m, pc]);
                        let sw_pr_pc = d.apply(swapped, &[pr, pc]);
                        let m_piv_pc = d.apply(m, &[piv, pc]);
                        let swapped_ne = {
                            let hyp = req(d, sw_pr_pc, zero_r);
                            let e_fv = d.fresh_fvar();
                            let e = d.kernel().fvar(e_fv);
                            let back = rsymm(d, sw_pr_pc, m_piv_pc, at_left_pc);
                            let chained = rtrans(d, m_piv_pc, sw_pr_pc, zero_r, back, e);
                            let contra = d.apply(piv_entry_ne, &[chained]);
                            d.lam_fv(e_fv, hyp, contra)
                        };

                        let le_refl = d.prelude().le_refl_thm;
                        let pr_le_pr = d.lemma(le_refl, &[pr]);

                        // The freshly-placed pivot row leads at exactly `pc`.
                        let li_cleared_pr = {
                            let nat_j = d.nat_ty();
                            let zero_left = {
                                let k_fv = d.fresh_fvar();
                                let k = d.kernel().fvar(k_fv);
                                let bound = NatOps::lt(d, k, pc);
                                let hk_fv = d.fresh_fvar();
                                let hk = d.kernel().fvar(hk_fv);
                                let off = d.lemma(
                                    p.clear_below_off,
                                    &[swapped, pr, pc, rows, pr, k, pr_le_pr],
                                );
                                let at_left = d.lemma(p.row_swap_at_left, &[pr, piv, m, k]);
                                let z = d.apply(hs[3], &[piv, k, pr_le_piv, piv_lt_rows, hk]);
                                let lhs = d.apply(cleared, &[pr, k]);
                                let mid = d.apply(swapped, &[pr, k]);
                                let rhs = d.apply(m, &[piv, k]);
                                let z0 = rzero(d, p);
                                let first = rtrans(d, lhs, mid, rhs, off, at_left);
                                let joined = rtrans(d, lhs, rhs, z0, first, z);
                                let with_hk = d.lam_fv(hk_fv, bound, joined);
                                d.lam_fv(k_fv, nat_j, with_hk)
                            };
                            let ne_at_pc = {
                                let off = d.lemma(
                                    p.clear_below_off,
                                    &[swapped, pr, pc, rows, pr, pc, pr_le_pr],
                                );
                                let cl_pr_pc = d.apply(cleared, &[pr, pc]);
                                let hyp = req(d, cl_pr_pc, zero_r);
                                let e_fv = d.fresh_fvar();
                                let e = d.kernel().fvar(e_fv);
                                let back = rsymm(d, cl_pr_pc, sw_pr_pc, off);
                                let chained = rtrans(d, sw_pr_pc, cl_pr_pc, zero_r, back, e);
                                let contra = d.apply(swapped_ne, &[chained]);
                                d.lam_fv(e_fv, hyp, contra)
                            };
                            d.lemma(
                                p.leading_index_eq_of_first_nonzero,
                                &[cleared, pr, cols, pc, pc_lt_cols, zero_left, ne_at_pc],
                            )
                        };

                        // A row already placed keeps its leading index.
                        let li_same = |d: &mut IntDev<'_>, r: ExprId, hr: ExprId| -> ExprId {
                            let nat_j = d.nat_ty();
                            let j_fv = d.fresh_fvar();
                            let j = d.kernel().fvar(j_fv);
                            let entry = d.lemma(
                                p.clear_below_row_swap_off,
                                &[m, pr, piv, pc, rows, r, j, hr, pr_le_piv],
                            );
                            let ptwise = d.lam_fv(j_fv, nat_j, entry);
                            d.lemma(p.leading_index_congr_row, &[cleared, m, r, r, cols, ptwise])
                        };

                        let next_h1 = {
                            let nat_j = d.nat_ty();
                            let r_fv = d.fresh_fvar();
                            let r = d.kernel().fvar(r_fv);
                            let sr = d.succ(r);
                            let bound = NatOps::lt(d, sr, spr);
                            let hr_fv = d.fresh_fvar();
                            let hr = d.kernel().fvar(hr_fv);

                            let lc_r = rleading_index(d, p, cleared, r, cols);
                            let lc_sr = rleading_index(d, p, cleared, sr, cols);
                            let target = {
                                let ok = d.const_app(p.echelon_step_ok, &[lc_r, lc_sr, cols]);
                                let t = d.bool_true();
                                d.bool_eq(ok, t)
                            };

                            let le_of_succ_le_succ = d.prelude().le_of_succ_le_succ;
                            let r_lt_pr = d.lemma(le_of_succ_le_succ, &[sr, pr, hr]);
                            let lt_or_eq_of_le = d.prelude().lt_or_eq_of_le;
                            let split = d.lemma(lt_or_eq_of_le, &[sr, pr, r_lt_pr]);
                            let lt_ty = NatOps::lt(d, sr, pr);
                            let eq_ty = d.eq(sr, pr);

                            let both_placed = {
                                let hx_fv = d.fresh_fvar();
                                let hx = d.kernel().fvar(hx_fv);
                                let e1 = li_same(d, r, r_lt_pr);
                                let e2 = li_same(d, sr, hx);
                                let base = d.apply(hs[1], &[r, hx]);
                                let lm_r = rleading_index(d, p, m, r, cols);
                                let lm_sr = rleading_index(d, p, m, sr, cols);
                                let e1_sym = NatOps::symm(d, lc_r, lm_r, e1);
                                let mid = nat_rewrite_prop(d, lm_r, lc_r, e1_sym, base, &|d, t| {
                                    let right = rleading_index(d, p, m, sr, cols);
                                    let ok = d.const_app(p.echelon_step_ok, &[t, right, cols]);
                                    let tv = d.bool_true();
                                    d.bool_eq(ok, tv)
                                });
                                let e2_sym = NatOps::symm(d, lc_sr, lm_sr, e2);
                                let moved =
                                    nat_rewrite_prop(d, lm_sr, lc_sr, e2_sym, mid, &|d, t| {
                                        let left = rleading_index(d, p, cleared, r, cols);
                                        let ok = d.const_app(p.echelon_step_ok, &[left, t, cols]);
                                        let tv = d.bool_true();
                                        d.bool_eq(ok, tv)
                                    });
                                d.lam_fv(hx_fv, lt_ty, moved)
                            };

                            let new_boundary = {
                                let he_fv = d.fresh_fvar();
                                let he = d.kernel().fvar(he_fv);
                                let e1 = li_same(d, r, r_lt_pr);
                                let lm_r = rleading_index(d, p, m, r, cols);
                                let h2r = d.apply(hs[2], &[r, r_lt_pr]);
                                let e1_sym = NatOps::symm(d, lc_r, lm_r, e1);
                                let lc_r_lt_pc =
                                    nat_rewrite_prop(d, lm_r, lc_r, e1_sym, h2r, &|d, t| {
                                        NatOps::lt(d, t, pc)
                                    });
                                let he_sym = NatOps::symm(d, sr, pr, he);
                                let li_at_sr =
                                    nat_rewrite_prop(d, pr, sr, he_sym, li_cleared_pr, &|d, t| {
                                        let l = rleading_index(d, p, cleared, t, cols);
                                        d.eq(l, pc)
                                    });
                                let base =
                                    d.lemma(p.echelon_step_ok_of_lt, &[lc_r, pc, cols, lc_r_lt_pc]);
                                let back = NatOps::symm(d, lc_sr, pc, li_at_sr);
                                let moved = nat_rewrite_prop(d, pc, lc_sr, back, base, &|d, t| {
                                    let left = rleading_index(d, p, cleared, r, cols);
                                    let ok = d.const_app(p.echelon_step_ok, &[left, t, cols]);
                                    let tv = d.bool_true();
                                    d.bool_eq(ok, tv)
                                });
                                d.lam_fv(he_fv, eq_ty, moved)
                            };

                            let chosen =
                                or_cases(d, lt_ty, eq_ty, target, both_placed, new_boundary, split);
                            let with_hr = d.lam_fv(hr_fv, bound, chosen);
                            d.lam_fv(r_fv, nat_j, with_hr)
                        };

                        let next_h2 = {
                            let nat_j = d.nat_ty();
                            let r_fv = d.fresh_fvar();
                            let r = d.kernel().fvar(r_fv);
                            let bound = NatOps::lt(d, r, spr);
                            let hr_fv = d.fresh_fvar();
                            let hr = d.kernel().fvar(hr_fv);
                            let lc_r = rleading_index(d, p, cleared, r, cols);
                            let target = NatOps::lt(d, lc_r, spc);

                            let le_of_succ_le_succ = d.prelude().le_of_succ_le_succ;
                            let r_le_pr = d.lemma(le_of_succ_le_succ, &[r, pr, hr]);
                            let lt_or_eq_of_le = d.prelude().lt_or_eq_of_le;
                            let split = d.lemma(lt_or_eq_of_le, &[r, pr, r_le_pr]);
                            let lt_ty = NatOps::lt(d, r, pr);
                            let eq_ty = d.eq(r, pr);

                            let already_placed = {
                                let hx_fv = d.fresh_fvar();
                                let hx = d.kernel().fvar(hx_fv);
                                let e1 = li_same(d, r, hx);
                                let lm_r = rleading_index(d, p, m, r, cols);
                                let h2r = d.apply(hs[2], &[r, hx]);
                                let slm = d.succ(lm_r);
                                let le_succ = d.prelude().le_succ;
                                let le_trans = d.prelude().le_trans;
                                let up = d.lemma(le_succ, &[pc]);
                                let widened = d.lemma(le_trans, &[slm, pc, spc, h2r, up]);
                                let e1_sym = NatOps::symm(d, lc_r, lm_r, e1);
                                let moved =
                                    nat_rewrite_prop(d, lm_r, lc_r, e1_sym, widened, &|d, t| {
                                        NatOps::lt(d, t, spc)
                                    });
                                d.lam_fv(hx_fv, lt_ty, moved)
                            };
                            let the_new_row = {
                                let he_fv = d.fresh_fvar();
                                let he = d.kernel().fvar(he_fv);
                                let he_sym = NatOps::symm(d, r, pr, he);
                                let li_at_r =
                                    nat_rewrite_prop(d, pr, r, he_sym, li_cleared_pr, &|d, t| {
                                        let l = rleading_index(d, p, cleared, t, cols);
                                        d.eq(l, pc)
                                    });
                                let lt_succ_self = d.prelude().lt_succ_self;
                                let base = d.lemma(lt_succ_self, &[pc]);
                                let back = NatOps::symm(d, lc_r, pc, li_at_r);
                                let moved = nat_rewrite_prop(d, pc, lc_r, back, base, &|d, t| {
                                    NatOps::lt(d, t, spc)
                                });
                                d.lam_fv(he_fv, eq_ty, moved)
                            };
                            let chosen = or_cases(
                                d,
                                lt_ty,
                                eq_ty,
                                target,
                                already_placed,
                                the_new_row,
                                split,
                            );
                            let with_hr = d.lam_fv(hr_fv, bound, chosen);
                            d.lam_fv(r_fv, nat_j, with_hr)
                        };

                        let next_h3 = {
                            let nat_j = d.nat_ty();
                            let s_fv = d.fresh_fvar();
                            let s = d.kernel().fvar(s_fv);
                            let c_fv = d.fresh_fvar();
                            let c = d.kernel().fvar(c_fv);
                            let lower = NatOps::le(d, spr, s);
                            let upper = NatOps::lt(d, s, rows);
                            let left = NatOps::lt(d, c, spc);
                            let hl_fv = d.fresh_fvar();
                            let hl = d.kernel().fvar(hl_fv);
                            let hu_fv = d.fresh_fvar();
                            let hu = d.kernel().fvar(hu_fv);
                            let hc_fv = d.fresh_fvar();
                            let hc = d.kernel().fvar(hc_fv);

                            let entry = d.apply(cleared, &[s, c]);
                            let target = req(d, entry, zero_r);

                            let le_of_succ_le_succ = d.prelude().le_of_succ_le_succ;
                            let c_le_pc = d.lemma(le_of_succ_le_succ, &[c, pc, hc]);
                            let lt_or_eq_of_le = d.prelude().lt_or_eq_of_le;
                            let split = d.lemma(lt_or_eq_of_le, &[c, pc, c_le_pc]);
                            let lt_ty = NatOps::lt(d, c, pc);
                            let eq_ty = d.eq(c, pc);

                            let old_column = {
                                let hx_fv = d.fresh_fvar();
                                let hx = d.kernel().fvar(hx_fv);
                                let range = {
                                    let t_fv = d.fresh_fvar();
                                    let t = d.kernel().fvar(t_fv);
                                    let lo = NatOps::le(d, pr, t);
                                    let hi = NatOps::lt(d, t, rows);
                                    let a_fv = d.fresh_fvar();
                                    let a = d.kernel().fvar(a_fv);
                                    let b_fv = d.fresh_fvar();
                                    let b = d.kernel().fvar(b_fv);
                                    let z = d.apply(hs[3], &[t, c, a, b, hx]);
                                    let with_b = d.lam_fv(b_fv, hi, z);
                                    let with_a = d.lam_fv(a_fv, lo, with_b);
                                    let f = d.lam_fv(t_fv, nat_j, with_a);
                                    d.lemma(
                                        p.row_swap_preserves_zero_range,
                                        &[m, pr, piv, rows, c, pr_le_piv, piv_lt_rows, f],
                                    )
                                };
                                let kept = d.lemma(
                                    p.clear_below_preserves_zero,
                                    &[swapped, pr, pc, rows, c, s, hl, hu, range],
                                );
                                d.lam_fv(hx_fv, lt_ty, kept)
                            };
                            let new_column = {
                                let he_fv = d.fresh_fvar();
                                let he = d.kernel().fvar(he_fv);
                                let at_pc = d.lemma(
                                    p.clear_below_zero,
                                    &[swapped, pr, pc, rows, s, hl, hu, swapped_ne],
                                );
                                let he_sym = NatOps::symm(d, c, pc, he);
                                let moved = nat_rewrite_prop(d, pc, c, he_sym, at_pc, &|d, t| {
                                    let e = d.apply(cleared, &[s, t]);
                                    let z = rzero(d, p);
                                    req(d, e, z)
                                });
                                d.lam_fv(he_fv, eq_ty, moved)
                            };
                            let chosen =
                                or_cases(d, lt_ty, eq_ty, target, old_column, new_column, split);
                            let with_hc = d.lam_fv(hc_fv, left, chosen);
                            let with_hu = d.lam_fv(hu_fv, upper, with_hc);
                            let with_hl = d.lam_fv(hl_fv, lower, with_hu);
                            let over_c = d.lam_fv(c_fv, nat_j, with_hl);
                            d.lam_fv(s_fv, nat_j, over_c)
                        };

                        let recursed = d.apply(
                            ih,
                            &[
                                cleared, spr, spc, pc_lt_cols, next_h1, next_h2, next_h3, next_fuel,
                            ],
                        );
                        let motive_x = d.bool_eq_motive(false_, &pivot_shape);
                        let hf_sym = d.bool_symm(no_pivot, false_, hf);
                        let inner = d.bool_transport(false_, motive_x, recursed, no_pivot, hf_sym);
                        d.lam_fv(hf_fv, pivot_false_ty, inner)
                    };

                    let pivot_split = bool_cases(d, no_pivot);
                    let chosen = or_cases(
                        d,
                        pivot_true_ty,
                        pivot_false_ty,
                        pivot_goal,
                        column_is_clear,
                        pivot_found,
                        pivot_split,
                    );
                    let motive_x = d.bool_eq_motive(false_, &cols_shape);
                    let hcf_sym = d.bool_symm(cols_done, false_, hcf);
                    let inner = d.bool_transport(false_, motive_x, chosen, cols_done, hcf_sym);
                    d.lam_fv(hcf_fv, cols_false_ty, inner)
                };

                let cols_split = bool_cases(d, cols_done);
                let chosen = or_cases(
                    d,
                    cols_true_ty,
                    cols_false_ty,
                    cols_goal,
                    stop_on_cols,
                    keep_going,
                    cols_split,
                );
                let motive_x = d.bool_eq_motive(false_, &rows_shape);
                let hrf_sym = d.bool_symm(rows_done, false_, hrf);
                let inner = d.bool_transport(false_, motive_x, chosen, rows_done, hrf_sym);
                d.lam_fv(hrf_fv, rows_false_ty, inner)
            };

            let rows_split = bool_cases(d, rows_done);
            or_cases(
                d,
                rows_true_ty,
                rows_false_ty,
                goal,
                stop_on_rows,
                rows_left,
                rows_split,
            )
        })
    };

    let fuel_fv = d.fresh_fvar();
    let fuel = d.kernel().fvar(fuel_fv);
    let proof = d.induct(&motive, &base, &step, fuel);
    let stmt = motive(d, fuel);

    let ty = {
        let over_fuel = d.pi_fv(fuel_fv, nat, stmt);
        let over_cols = d.pi_fv(cols_fv, nat, over_fuel);
        d.pi_fv(rows_fv, nat, over_cols)
    };
    let value = {
        let over_fuel = d.lam_fv(fuel_fv, nat, proof);
        let over_cols = d.lam_fv(cols_fv, nat, over_fuel);
        d.lam_fv(rows_fv, nat, over_cols)
    };
    d.declare_theorem(p.echelon_aux_is_echelon, ty, value)
}

/// Admit `Rat.rowEchelon_isEchelon : ∀ M rows cols,
/// Eq Bool (isEchelon (rowEchelon M rows cols) rows cols) true`.
///
/// **ADR-1554 obligation 4, unconditional.** `rowEchelon` starts both cursors
/// at `0`, where three of the five invariant clauses are vacuous — `Lt _ 0` has
/// no inhabitant — the fourth is `Nat.zero_le` and the fifth is
/// `Le cols (Nat.add 0 cols)`, one `Nat.zero_add`.
///
/// That the entry point needs NO hypothesis is the whole point of stating the
/// loop lemma over arbitrary cursors: the invariant is trivially true where the
/// loop starts, and everything else is the induction.
fn declare_row_echelon_is_echelon(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let mty = mat_ty(d);

    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let rows_fv = d.fresh_fvar();
    let rows = d.kernel().fvar(rows_fv);
    let cols_fv = d.fresh_fvar();
    let cols = d.kernel().fvar(cols_fv);

    let zero_n = d.zero();
    let answer = d.const_app(p.row_echelon, &[m, rows, cols]);
    let scanned = d.const_app(p.is_echelon, &[answer, rows, cols]);
    let true_ = d.bool_true();
    let concl = d.bool_eq(scanned, true_);

    let zero_le = d.prelude().zero_le;
    let h0 = d.lemma(zero_le, &[cols]);

    // `Lt (succ r) 0` and `Lt r 0` have no inhabitants, and neither does
    // `Lt c 0` — so H1, H2 and H3 are all discharged by `Nat.not_succ_le_zero`.
    let not_succ_le_zero = d.prelude().not_succ_le_zero;

    let h1 = {
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        let sr = d.succ(r);
        let bound = NatOps::lt(d, sr, zero_n);
        let hr_fv = d.fresh_fvar();
        let hr = d.kernel().fvar(hr_fv);
        let l1 = rleading_index(d, p, m, r, cols);
        let l2 = rleading_index(d, p, m, sr, cols);
        let ok = d.const_app(p.echelon_step_ok, &[l1, l2, cols]);
        let tv = d.bool_true();
        let target = d.bool_eq(ok, tv);
        let refutation = d.lemma(not_succ_le_zero, &[sr]);
        let contradiction = d.apply(refutation, &[hr]);
        let body = absurd(d, target, contradiction);
        let with_hr = d.lam_fv(hr_fv, bound, body);
        d.lam_fv(r_fv, nat, with_hr)
    };

    let h2 = {
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        let bound = NatOps::lt(d, r, zero_n);
        let hr_fv = d.fresh_fvar();
        let hr = d.kernel().fvar(hr_fv);
        let l = rleading_index(d, p, m, r, cols);
        let target = NatOps::lt(d, l, zero_n);
        let refutation = d.lemma(not_succ_le_zero, &[r]);
        let contradiction = d.apply(refutation, &[hr]);
        let body = absurd(d, target, contradiction);
        let with_hr = d.lam_fv(hr_fv, bound, body);
        d.lam_fv(r_fv, nat, with_hr)
    };

    let h3 = {
        let s_fv = d.fresh_fvar();
        let s = d.kernel().fvar(s_fv);
        let c_fv = d.fresh_fvar();
        let c = d.kernel().fvar(c_fv);
        let lower = NatOps::le(d, zero_n, s);
        let upper = NatOps::lt(d, s, rows);
        let left = NatOps::lt(d, c, zero_n);
        let hl_fv = d.fresh_fvar();
        let hu_fv = d.fresh_fvar();
        let hc_fv = d.fresh_fvar();
        let hc = d.kernel().fvar(hc_fv);
        let entry = d.apply(m, &[s, c]);
        let z = rzero(d, p);
        let target = req(d, entry, z);
        let refutation = d.lemma(not_succ_le_zero, &[c]);
        let contradiction = d.apply(refutation, &[hc]);
        let body = absurd(d, target, contradiction);
        let with_hc = d.lam_fv(hc_fv, left, body);
        let with_hu = d.lam_fv(hu_fv, upper, with_hc);
        let with_hl = d.lam_fv(hl_fv, lower, with_hu);
        let over_c = d.lam_fv(c_fv, nat, with_hl);
        d.lam_fv(s_fv, nat, over_c)
    };

    let h4 = {
        let sum = NatOps::add(d, zero_n, cols);
        let zero_add = d.prelude().zero_add;
        let za = d.lemma(zero_add, &[cols]);
        let za_sym = NatOps::symm(d, sum, cols, za);
        let le_refl = d.prelude().le_refl_thm;
        let base = d.lemma(le_refl, &[cols]);
        nat_rewrite_prop(d, cols, sum, za_sym, base, &|d, t| NatOps::le(d, cols, t))
    };

    let aux = d.lemma(
        p.echelon_aux_is_echelon,
        &[rows, cols, cols, m, zero_n, zero_n],
    );
    let proof = d.apply(aux, &[h0, h1, h2, h3, h4]);

    let ty = {
        let over_cols = d.pi_fv(cols_fv, nat, concl);
        let over_rows = d.pi_fv(rows_fv, nat, over_cols);
        d.pi_fv(m_fv, mty, over_rows)
    };
    let value = {
        let over_cols = d.lam_fv(cols_fv, nat, proof);
        let over_rows = d.lam_fv(rows_fv, nat, over_cols);
        d.lam_fv(m_fv, mty, over_rows)
    };
    d.declare_theorem(p.row_echelon_is_echelon, ty, value)
}
