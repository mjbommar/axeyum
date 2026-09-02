//! `Rat.pivotSearch_ne_zero` — the **value half** of ADR-1554's obligation 2,
//! the other half of `Rat.pivotSearch`'s postcondition (ADR-1562).
//!
//! ## What this is, next to [`super::pivot_bound`]
//!
//! ADR-1554 states obligation 2 as a disjunction:
//!
//! > the returned index is either `rows`, and then every entry of column `c` in
//! > `[start, rows)` is zero; or it is in `[start, rows)` with a nonzero entry
//! > there.
//!
//! `pivot_bound.rs` landed the RANGE half — `result ≤ rows` — which both
//! disjuncts assert and neither the `Or` nor the bounded `∀` is needed for.
//! This file lands the **value half of the second disjunct**:
//!
//! ```text
//! Rat.pivotSearchAux_ne_zero : ∀ M c rows fuel r,
//!   Lt (pivotSearchAux M c rows fuel r) rows →
//!     Not (Eq Rat (M (pivotSearchAux M c rows fuel r) c) Rat.zero)
//! Rat.pivotSearch_ne_zero    : the same at the fuel and start `pivotSearch` picks
//! ```
//!
//! *"If the search landed in range, the entry it landed on is nonzero."* This
//! is the half **obligation 3 spends**: `clearBelow`'s arithmetic core is
//! `a + (-(a/b)) * b = 0` given `b ≠ 0`, and `b` is exactly this pivot entry,
//! consumed through `Rat.mul_inv_cancel_of_ne_zero`.
//!
//! ## What is still missing from obligation 2
//!
//! The FIRST disjunct — *the answer is `rows` and then column `c` is zero
//! throughout `[start, rows)`* — is not here. It is a bounded `∀` over the
//! scanned range, and unlike everything in this file it does not follow from
//! looking at the single index the scan returned: it is a statement about every
//! index the scan passed. It needs the fuel induction to carry the accumulated
//! range in its motive, which is a different induction, not a stronger form of
//! this one.
//!
//! So obligation 2 now stands as: range half landed (`pivot_bound.rs`), value
//! half landed (here), the exhaustion disjunct open.
//!
//! ## The route, and why it is short
//!
//! Exactly the shape of `Rat.pivotRowSearchAux_leadingIndex`
//! (`rank_bridge.rs`): a fuel induction whose motive is an IMPLICATION, with
//! the row index generalised inside it. The in-range hypothesis carries
//! everything — both exhaustion answers are `rows` itself, which
//! `Nat.lt_irrefl` refutes, so the two "gave up" branches are discharged
//! without knowing anything about the matrix, and the only branch that does any
//! work is the one where the zero test came back `false`.
//!
//! Both splits need their hypothesis here (as in that sibling, and unlike
//! `Rat.pivotColSearchAux_eq_ble` whose inner split is free): the inner `false`
//! branch carries the whole conclusion, through
//! `Rat.ne_zero_of_isZeroB_false`.

use super::RatPrelude;
use super::echelon::{bool_select_at, ris_zero_b};
use super::matrix_det::mat_ty;
use super::ops::{rat_ty, rzero};
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
pub(super) fn declare_pivot_content(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    declare_pivot_search_aux_ne_zero(d, p)?;
    declare_pivot_search_ne_zero(d, p)?;
    Ok(())
}

/// `Not (Eq Rat (M r c) Rat.zero)` — the conclusion, at an arbitrary row.
fn entry_ne_zero(d: &mut IntDev<'_>, p: RatPrelude, m: ExprId, r: ExprId, c: ExprId) -> ExprId {
    let entry = d.apply(m, &[r, c]);
    let zero_r = rzero(d, p);
    let rat = rat_ty(d);
    let one = d.level_one();
    let eq_name = d.prelude().logic.eq;
    let eq = d.kernel().const_(eq_name, vec![one]);
    let equation = d.apply(eq, &[rat, entry, zero_r]);
    d.not(equation)
}

/// Admit `Rat.pivotSearchAux_ne_zero : ∀ M c rows fuel r,
/// Lt (pivotSearchAux M c rows fuel r) rows →
///   Not (Eq Rat (M (pivotSearchAux M c rows fuel r) c) Rat.zero)`.
///
/// See the module note for the route. `M`, `c` and `rows` are fixed outside the
/// induction; `r` is generalised INSIDE the motive, because the step
/// instantiates its hypothesis at `succ r`.
fn declare_pivot_search_aux_ne_zero(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let mty = mat_ty(d);

    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let rows_fv = d.fresh_fvar();
    let rows = d.kernel().fvar(rows_fv);
    let fuel_fv = d.fresh_fvar();
    let fuel = d.kernel().fvar(fuel_fv);

    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        let found = d.const_app(p.pivot_search_aux, &[m, c, rows, x, r]);
        let hyp = NatOps::lt(d, found, rows);
        let concl = entry_ne_zero(d, p, m, found, c);
        let body = d.arrow(hyp, concl);
        d.pi_fv(r_fv, nat, body)
    };
    let stmt = motive(d, fuel);

    // Both exhaustion answers are `rows`, so `Lt rows rows` refutes them.
    let refute_at_rows = |d: &mut IntDev<'_>| -> ExprId {
        let hyp = NatOps::lt(d, rows, rows);
        let concl = entry_ne_zero(d, p, m, rows, c);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let lt_irrefl = d.prelude().lt_irrefl;
        let refutation = d.lemma(lt_irrefl, &[rows]);
        let contradiction = d.apply(refutation, &[h]);
        let inner = absurd(d, concl, contradiction);
        d.lam_fv(h_fv, hyp, inner)
    };

    let base = |d: &mut IntDev<'_>| -> ExprId {
        let r_fv = d.fresh_fvar();
        let body = refute_at_rows(d);
        d.lam_fv(r_fv, nat, body)
    };

    let step = |d: &mut IntDev<'_>, jf: ExprId, ih: ExprId| -> ExprId {
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);

        let entry = d.apply(m, &[r, c]);
        let is_zero = ris_zero_b(d, p, entry);
        let sr = d.succ(r);
        let recursed = d.const_app(p.pivot_search_aux, &[m, c, rows, jf, sr]);
        let inner_row = bool_select_at(d, nat, is_zero, recursed, r);
        let oor = NatOps::ble(d, rows, r);
        let outer_row = bool_select_at(d, nat, oor, rows, inner_row);

        let goal = {
            let hyp = NatOps::lt(d, outer_row, rows);
            let concl = entry_ne_zero(d, p, m, outer_row, c);
            d.arrow(hyp, concl)
        };

        let true_ = d.bool_true();
        let false_ = d.bool_false();
        let h_true_ty = d.bool_eq(oor, true_);
        let h_false_ty = d.bool_eq(oor, false_);

        let outer_shape = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
            let chosen = bool_select_at(d, nat, x, rows, inner_row);
            let hyp = NatOps::lt(d, chosen, rows);
            let concl = entry_ne_zero(d, p, m, chosen, c);
            d.arrow(hyp, concl)
        };

        let left_minor = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let motive_x = d.bool_eq_motive(true_, &outer_shape);
            let refl_case = refute_at_rows(d);
            let h_sym = d.bool_symm(oor, true_, h);
            let body = d.bool_transport(true_, motive_x, refl_case, oor, h_sym);
            d.lam_fv(h_fv, h_true_ty, body)
        };

        let right_minor = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);

            let inner_shape = |d: &mut IntDev<'_>, y: ExprId| -> ExprId {
                let chosen = bool_select_at(d, nat, y, recursed, r);
                let hyp = NatOps::lt(d, chosen, rows);
                let concl = entry_ne_zero(d, p, m, chosen, c);
                d.arrow(hyp, concl)
            };

            let zero_true_ty = d.bool_eq(is_zero, true_);
            let zero_false_ty = d.bool_eq(is_zero, false_);
            let inner_goal = inner_shape(d, is_zero);

            let zero_left = {
                let hh_fv = d.fresh_fvar();
                let hh = d.kernel().fvar(hh_fv);
                let motive_y = d.bool_eq_motive(true_, &inner_shape);
                let refl_case = d.apply(ih, &[sr]);
                let hh_sym = d.bool_symm(is_zero, true_, hh);
                let body = d.bool_transport(true_, motive_y, refl_case, is_zero, hh_sym);
                d.lam_fv(hh_fv, zero_true_ty, body)
            };
            let zero_right = {
                let hh_fv = d.fresh_fvar();
                let hh = d.kernel().fvar(hh_fv);
                let motive_y = d.bool_eq_motive(false_, &inner_shape);
                let refl_case = {
                    let hyp = NatOps::lt(d, r, rows);
                    let ignored_fv = d.fresh_fvar();
                    let ne_zero = d.lemma(p.ne_zero_of_is_zero_b_false, &[entry, hh]);
                    d.lam_fv(ignored_fv, hyp, ne_zero)
                };
                let hh_sym = d.bool_symm(is_zero, false_, hh);
                let body = d.bool_transport(false_, motive_y, refl_case, is_zero, hh_sym);
                d.lam_fv(hh_fv, zero_false_ty, body)
            };

            let zero_split = bool_cases(d, is_zero);
            let inner_proof = or_cases(
                d,
                zero_true_ty,
                zero_false_ty,
                inner_goal,
                zero_left,
                zero_right,
                zero_split,
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
    d.declare_theorem(p.pivot_search_aux_ne_zero, ty, value)
}

/// Admit `Rat.pivotSearch_ne_zero : ∀ M c start rows,
/// Lt (pivotSearch M c start rows) rows →
///   Not (Eq Rat (M (pivotSearch M c start rows) c) Rat.zero)`.
///
/// [`declare_pivot_search_aux_ne_zero`] at the fuel and start index
/// `pivotSearch` picks. As with the range half, **no bound on `start` is
/// needed**: a `start` already past `rows` returns `rows` on its first step, and
/// the in-range hypothesis then refutes itself.
fn declare_pivot_search_ne_zero(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
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
    let concl = entry_ne_zero(d, p, m, found, c);
    let stmt = d.arrow(hyp_ty, concl);

    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);
    let aux = d.lemma(p.pivot_search_aux_ne_zero, &[m, c, rows, rows]);
    let at_start = d.apply(aux, &[start]);
    let body = d.apply(at_start, &[h]);
    let proof = d.lam_fv(h_fv, hyp_ty, body);

    let ty = {
        let over_rows = d.pi_fv(rows_fv, nat, stmt);
        let over_start = d.pi_fv(start_fv, nat, over_rows);
        let over_c = d.pi_fv(c_fv, nat, over_start);
        d.pi_fv(m_fv, mty, over_c)
    };
    let value = {
        let over_rows = d.lam_fv(rows_fv, nat, proof);
        let over_start = d.lam_fv(start_fv, nat, over_rows);
        let over_c = d.lam_fv(c_fv, nat, over_start);
        d.lam_fv(m_fv, mty, over_c)
    };
    d.declare_theorem(p.pivot_search_ne_zero, ty, value)
}
