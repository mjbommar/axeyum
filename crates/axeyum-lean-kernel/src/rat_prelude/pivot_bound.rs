//! `Rat.pivotSearch_le_rows` — the range half of ADR-1554's **obligation 2**,
//! the postcondition of `Rat.pivotSearch` (ADR-1558 §3).
//!
//! ## What this is a slice of
//!
//! ADR-1554 sizes `rowEchelon_isEchelon` as four obligations. Obligation 2 is
//! `pivotSearch`'s postcondition, stated there as a disjunction:
//!
//! > the returned index is either `rows`, and then every entry of column `c` in
//! > `[start, rows)` is zero; or it is in `[start, rows)` with a nonzero entry
//! > there.
//!
//! Both disjuncts assert `result ≤ rows`, and neither the `Or` nor the bounded
//! `∀` is needed to prove that much. So the **range half** — *the search never
//! returns an index past the row count* — is a self-contained sub-obligation,
//! and it is the one landed here:
//!
//! ```text
//! Rat.pivotSearchAux_le_rows : ∀ M c rows fuel r, Le (pivotSearchAux M c rows fuel r) rows
//! Rat.pivotSearch_le_rows    : ∀ M c start rows,  Le (pivotSearch M c start rows) rows
//! ```
//!
//! What is NOT here is the *content* half: which of the two disjuncts holds,
//! and the bounded statement about the entries. That needs
//! `Rat.eq_zero_of_isZeroB` / `Rat.ne_zero_of_isZeroB_false` (obligation 1,
//! landed by `rat-echelon`) carried through the same fuel induction with an
//! `Or` in the motive, and it remains open.
//!
//! ## The route, and the one lemma the ℕ prelude was missing
//!
//! Induction on the fuel with the row index generalised — `r` moves in the
//! recursion, so the motive is `∀ r, Le (pivotSearchAux … x r) rows` and the
//! step instantiates its hypothesis at `succ r`. Both exhaustion answers are
//! `rows` itself, so the base case is `Nat.le_refl`.
//!
//! The step splits twice. The **inner** split, on `isZeroB (M r c)`, needs no
//! hypothesis at all: whichever way it goes, one branch is the induction
//! hypothesis at `succ r` and the other is the row index `r`, and both are
//! already bounded. It is therefore a bare `Bool.rec` at a `Prop` motive
//! ([`le_select`]) rather than a case analysis.
//!
//! The **outer** split, on `Nat.ble rows r`, does need its hypothesis — in the
//! `false` branch the answer is `r`, and `Le r rows` is simply false without
//! it. That is where the one missing ingredient shows up: **`Nat` has
//! `le_of_ble_eq_true` but no `le_of_ble_eq_false`.** The `ipc` prelude has
//! exactly the statement (`ipc_le_of_ble_eq_false`) and the `rat` build does
//! not carry it, so [`le_of_ble_false`] rebuilds it here as an inline step from
//! `Nat.le_total` and `Nat.ble_eq_true_of_le`: the two orderings are
//! exhaustive, and the one that contradicts the hypothesis is discharged
//! through `Bool.true_ne_false`. It is an inline step and not a declaration on
//! purpose — it is a `Nat` fact, and a `Rat`-namespaced declaration of a `Nat`
//! fact is the naming hazard `CLAUDE.md` warns about. If a second consumer
//! appears it belongs in `nat_prelude`, not here.

use super::RatPrelude;
use super::echelon::bool_select_at;
use super::matrix_det::mat_ty;
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
pub(super) fn declare_pivot_bound(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    declare_pivot_search_aux_le_rows(d, p)?;
    declare_pivot_search_le_rows(d, p)?;
    Ok(())
}

// --- devices ---------------------------------------------------------------

/// `Or (Eq Bool b true) (Eq Bool b false)` — the two-way case analysis on a
/// `Bool`, at `IntDev`.
///
/// `nat_prelude::ops::bool_true_or_false` is the same term, but its signature
/// is `NatDev`-specific and this file runs at `IntDev`.
fn bool_cases(d: &mut IntDev<'_>, b: ExprId) -> ExprId {
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

/// `Eq Bool (Nat.ble a b) Bool.false ⊢ Le b a`.
///
/// The `Nat` prelude has `le_of_ble_eq_true` and NOT its false-side twin; see
/// the module note. Route: `Nat.le_total b a` is exhaustive, and the `Le a b`
/// disjunct gives `ble a b = true` through `Nat.ble_eq_true_of_le`, which
/// contradicts the hypothesis via `Bool.true_ne_false`.
fn le_of_ble_false(d: &mut IntDev<'_>, a: ExprId, b: ExprId, h: ExprId) -> ExprId {
    let goal = NatOps::le(d, b, a);

    let le_ba = NatOps::le(d, b, a);
    let le_ab = NatOps::le(d, a, b);

    let left_minor = {
        let hl_fv = d.fresh_fvar();
        let hl = d.kernel().fvar(hl_fv);
        d.lam_fv(hl_fv, le_ba, hl)
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

    let le_total = d.prelude().le_total;
    let split = d.lemma(le_total, &[b, a]);
    or_cases(d, le_ba, le_ab, goal, left_minor, right_minor, split)
}

/// `Le (bool_select_at Nat b on_true on_false) bound` from a proof for each
/// branch — a bare `Bool.rec` at a `Prop` motive, no hypothesis about `b`.
///
/// This is what makes the inner split of the step case free: neither branch
/// needs to know which way the test went.
fn le_select(
    d: &mut IntDev<'_>,
    b: ExprId,
    on_true: ExprId,
    on_false: ExprId,
    bound: ExprId,
    proof_true: ExprId,
    proof_false: ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let bool_ty = d.bool_ty();
    let motive = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let selected = bool_select_at(d, nat, x, on_true, on_false);
        let body = NatOps::le(d, selected, bound);
        d.lam_fv(x_fv, bool_ty, body)
    };
    let level_zero = d.kernel().level_zero();
    let bool_rec_name = d.prelude().logic.bool_rec;
    let bool_rec = d.kernel().const_(bool_rec_name, vec![level_zero]);
    d.apply(bool_rec, &[motive, proof_false, proof_true, b])
}

// --- the range bound -------------------------------------------------------

/// Admit `Rat.pivotSearchAux_le_rows : ∀ M c rows fuel r,
/// Le (pivotSearchAux M c rows fuel r) rows`.
///
/// See the module note for the route. `M`, `c` and `rows` are fixed outside the
/// induction; `r` is generalised INSIDE the motive, because the step
/// instantiates its hypothesis at `succ r` rather than at `r`.
fn declare_pivot_search_aux_le_rows(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
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
        let value = d.const_app(p.pivot_search_aux, &[m, c, rows, x, r]);
        let body = NatOps::le(d, value, rows);
        d.pi_fv(r_fv, nat, body)
    };
    let stmt = motive(d, fuel);

    let base = |d: &mut IntDev<'_>| -> ExprId {
        let r_fv = d.fresh_fvar();
        let le_refl = d.prelude().le_refl;
        let body = d.lemma(le_refl, &[rows]);
        d.lam_fv(r_fv, nat, body)
    };

    let step = |d: &mut IntDev<'_>, j: ExprId, ih: ExprId| -> ExprId {
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);

        // The two branch values, in the shape `pivotSearchAux`'s successor case
        // builds them.
        let entry = d.apply(m, &[r, c]);
        let b2 = d.const_app(p.is_zero_b, &[entry]);
        let sr = d.succ(r);
        let recursed = d.const_app(p.pivot_search_aux, &[m, c, rows, j, sr]);
        let inner = bool_select_at(d, nat, b2, recursed, r);
        let b1 = NatOps::ble(d, rows, r);
        let outer = bool_select_at(d, nat, b1, rows, inner);

        let goal = NatOps::le(d, outer, rows);

        // Outer split on `ble rows r`. Only the FALSE branch needs its
        // hypothesis, but the transport is symmetric so both are written the
        // same way.
        let true_ = d.bool_true();
        let false_ = d.bool_false();
        let h_true_ty = d.bool_eq(b1, true_);
        let h_false_ty = d.bool_eq(b1, false_);

        let left_minor = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let motive_x = d.bool_eq_motive(true_, &|d, x| {
                let selected = bool_select_at(d, nat, x, rows, inner);
                NatOps::le(d, selected, rows)
            });
            let le_refl = d.prelude().le_refl;
            let refl_case = d.lemma(le_refl, &[rows]);
            let h_sym = d.bool_symm(b1, true_, h);
            let body = d.bool_transport(true_, motive_x, refl_case, b1, h_sym);
            d.lam_fv(h_fv, h_true_ty, body)
        };

        let right_minor = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);

            // `Le inner rows`, with no case analysis on `isZeroB`.
            let proof_true = d.apply(ih, &[sr]);
            let proof_false = le_of_ble_false(d, rows, r, h);
            let inner_proof = le_select(d, b2, recursed, r, rows, proof_true, proof_false);

            let motive_x = d.bool_eq_motive(false_, &|d, x| {
                let selected = bool_select_at(d, nat, x, rows, inner);
                NatOps::le(d, selected, rows)
            });
            let h_sym = d.bool_symm(b1, false_, h);
            let body = d.bool_transport(false_, motive_x, inner_proof, b1, h_sym);
            d.lam_fv(h_fv, h_false_ty, body)
        };

        let split = bool_cases(d, b1);
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
    d.declare_theorem(p.pivot_search_aux_le_rows, ty, value)
}

/// Admit `Rat.pivotSearch_le_rows : ∀ M c start rows,
/// Le (pivotSearch M c start rows) rows`.
///
/// [`declare_pivot_search_aux_le_rows`] at the fuel `pivotSearch` picks. Note
/// that no bound on `start` is needed: a `start` already past `rows` takes the
/// out-of-range branch on its first step and returns `rows`.
fn declare_pivot_search_le_rows(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
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

    let value_term = d.const_app(p.pivot_search, &[m, c, start, rows]);
    let stmt = NatOps::le(d, value_term, rows);

    let aux_bound = d.lemma(p.pivot_search_aux_le_rows, &[m, c, rows, rows]);
    let proof = d.apply(aux_bound, &[start]);

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
    d.declare_theorem(p.pivot_search_le_rows, ty, value)
}
