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
use super::echelon::{bool_select_at, ris_zero_b, rrow_swap};
use super::matrix_det::mat_ty;
use super::ops::{nat_rewrite_prop, rat_eq_rewrite, req, rtrans, rzero};
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
    declare_leading_index_aux_congr_row(d, p)?;
    declare_leading_index_congr_row(d, p)?;
    declare_clear_below_row_swap_off(d, p)?;
    Ok(())
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
