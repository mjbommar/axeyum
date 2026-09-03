//! ADR-1554 obligation 4 — the row-swap half of the loop invariant.
//!
//! ADR-1571 §3 measured what `echelonAux`'s loop invariant needs and found one
//! prerequisite missing: the pivot step SWAPS before it sweeps, and the swap
//! moves two rows that both live in the range `[pr, rows)` the invariant claims
//! is zero to the left of the cursor. `Rat.clearBelow_preserves_zero` covers
//! the sweep; nothing covered the swap.
//!
//! ```text
//! Rat.rowSwap_preserves_zero_range :
//!   ∀ M pr piv rows k, Le pr piv → Lt piv rows →
//!     (∀ s, Le pr s → Lt s rows → Eq Rat (M s k) Rat.zero) →
//!     ∀ s, Le pr s → Lt s rows → Eq Rat (rowSwap pr piv M s k) Rat.zero
//! ```
//!
//! ## Why the two bounds on `piv` are hypotheses and not derived
//!
//! `rowSwap pr piv M` reads row `piv` into position `pr`, so the conclusion at
//! `s = pr` is a claim about `M piv k` — and the hypothesis only speaks about
//! rows in `[pr, rows)`. Both `Le pr piv` and `Lt piv rows` are therefore load
//! bearing, and they are exactly what the caller has: `echelonAux` takes this
//! branch only when `Nat.ble rows piv = false`, and the search that produced
//! `piv` started at `pr`.
//!
//! `Lt pr rows` is NOT a hypothesis: it follows from the two that are, by
//! `Nat.lt_of_le_of_lt`, and it is needed only in the `s = piv` branch where
//! the answer is `M pr k`.
//!
//! ## The splits, and why neither is free
//!
//! ADR-1562 §3's rule — *a split is free exactly when neither branch's proof
//! mentions the tested `Bool`* — does not apply here. Both branches of
//! `Nat.beq s pr` produce a DIFFERENT equation for `rowSwap … s k`
//! (`rowSwap_at_left` vs. the other two), and the inner split on
//! `Nat.beq s piv` is worse than not free: `Rat.rowSwap_at_right` needs
//! `Nat.beq piv pr = false`, which is the OUTER split's `false` hypothesis
//! transported along `s = piv`. That transport is the only real step in the
//! proof, and it is why the outer test is `beq s pr` rather than `beq s piv`:
//! with the tests the other way round the inner branch would have to produce
//! `Nat.beq piv pr = false` out of nothing.

use super::RatPrelude;
use super::echelon::rrow_swap;
use super::matrix_det::mat_ty;
use super::ops::{nat_rewrite_prop, req, rtrans, rzero};
use super::rank_bridge::bool_cases;
use crate::KernelError;
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::NatOps;
use crate::nat_prelude::steps::or_cases;

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
    Ok(())
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
