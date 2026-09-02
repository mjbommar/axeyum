//! Row-echelon form over `ℚ` — the three elementary row operations, a
//! **computed** Gaussian elimination, and the decidable predicate that says
//! when a matrix is in echelon form (ADR-1554).
//!
//! ## Why this exists
//!
//! `Rat.rank` does not exist, and the dominance document concedes it. Rank is
//! read off a row-echelon form, and rank-nullity follows from the same
//! construction, so the echelon form is the piece that has to land first. This
//! module is the first of three: it builds the form and the invertibility of
//! each operation, and deliberately does **not** attempt `rank`.
//!
//! ## Computed, not extracted
//!
//! Every step here is a `Definition` the kernel REDUCES. The pivot is found by
//! a bounded search that returns a `Nat` — never by eliminating an `Exists` and
//! extracting a witness. `Nat.lnp_bounded_search` is the least-number principle
//! and is the right tool for *proving* a least element exists; it cannot drive
//! a computation, because its conclusion is an `Or` of `Prop`s. The distinction
//! matters twice over:
//!
//! - a `Prop`-valued `Eq x 0` cannot branch a definition, so the zero test is
//!   [`RatPrelude::is_zero_b`], `Bool`-valued and total, built from `Rat.ble`
//!   alone. Over `ℚ` the order is decidable and this is a plain function; no
//!   `Decidable` instance, no choice, no axiom;
//! - and the evaluation tests can then *run* `rowEchelon` at a concrete 2×2 and
//!   read the answer off, which is the only thing that can tell you a
//!   definition computes the wrong value. The trusted gate cannot: every one of
//!   these has the right type whatever it returns.
//!
//! ## Fuel, and why `cols` is exact
//!
//! [`RatPrelude::echelon_aux`] takes a fuel counter and structurally recurses
//! on it, because the loop is not structural in any of its real arguments.
//! [`RatPrelude::row_echelon`] instantiates it at `cols`, and that is EXACT
//! rather than generous: the pivot column `pc` advances on **every** iteration
//! — both when a pivot is found and when the column turns out to be all zero —
//! so after `cols` steps the `pc < cols` guard has certainly fired and no
//! further step is possible. The inner sweeps take fuel `rows` for the same
//! reason.
//!
//! Keeping the fuel at `cols` rather than `rows * cols` matters here and not
//! only for tidiness: every `Nat` numeral this prelude builds is unary, so a
//! magnitude formed is a magnitude walked.
//!
//! ## What the next lane needs
//!
//! `rank` reads [`RatPrelude::leading_index`] over the rows of
//! [`RatPrelude::row_echelon`] and counts the rows whose leading index is below
//! `cols`. Rank INVARIANCE consumes the three inverse laws in this file —
//! [`RatPrelude::row_swap_involutive`], [`RatPrelude::row_add_mul_inverse`] and
//! [`RatPrelude::row_scale_inverse`] — which is what makes each elementary
//! operation a bijection on matrices and therefore rank-preserving.

use super::RatPrelude;
use super::matrix_det::{bool_cases_eq, mat_ty};
use super::ops::{
    nat_eq_to_rat, nat_rewrite_prop, radd, rat_eq_rewrite, rat_ty, rchain, rcongr, req, rmul, rneg,
    rone, rsymm, rtrans, rzero,
};
use crate::BinderInfo;
use crate::KernelError;
use crate::env::{Declaration, ReducibilityHint};
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::NatOps;

/// Delta height for [`RatPrelude::is_zero_b`] and
/// [`RatPrelude::echelon_step_ok`]: above `Rat.ble` and `Nat.ble`, the only
/// constants they unfold to.
const LEAF_HEIGHT: u16 = 55;

/// Delta height for the three elementary row operations, one above
/// `Rat.matSetRow`'s 53 and `Rat.matSubstRows`'s 54 so a row operation unfolds
/// before the `matSetRow` write underneath it.
const ROW_OP_HEIGHT: u16 = 56;

/// Delta height for the two fuelled searches, which call [`LEAF_HEIGHT`].
const SEARCH_AUX_HEIGHT: u16 = 57;

/// Delta height for the search wrappers and the elimination sweep.
const SWEEP_HEIGHT: u16 = 58;

/// Delta height for the sweep wrapper and the echelon predicate's recursion.
const SWEEP_WRAP_HEIGHT: u16 = 59;

/// Delta height for the driver loop and the echelon predicate.
const DRIVER_HEIGHT: u16 = 60;

/// Delta height for [`RatPrelude::row_echelon`], the outermost entry point.
const ENTRY_HEIGHT: u16 = 61;

/// Declare everything this file builds.
///
/// # Errors
///
/// Returns the trusted gate's rejection — an `Err` means the kernel
/// **refused** a declaration, not that a script gave up.
pub(super) fn declare_echelon(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    declare_is_zero_b(d, p)?;
    declare_is_zero_b_zero(d, p)?;
    declare_eq_zero_of_is_zero_b(d, p)?;
    declare_is_zero_b_of_eq_zero(d, p)?;
    declare_ne_zero_of_is_zero_b_false(d, p)?;
    declare_row_swap(d, p)?;
    declare_row_scale(d, p)?;
    declare_row_add_mul(d, p)?;
    declare_row_swap_at_left(d, p)?;
    declare_row_swap_at_right(d, p)?;
    declare_row_swap_off(d, p)?;
    declare_row_scale_at(d, p)?;
    declare_row_scale_off(d, p)?;
    declare_row_add_mul_at(d, p)?;
    declare_row_add_mul_off(d, p)?;
    declare_row_swap_involutive(d, p)?;
    declare_row_add_mul_inverse(d, p)?;
    declare_row_scale_inverse(d, p)?;
    declare_pivot_search_aux(d, p)?;
    declare_pivot_search(d, p)?;
    declare_clear_below_aux(d, p)?;
    declare_clear_below(d, p)?;
    declare_echelon_aux(d, p)?;
    declare_row_echelon(d, p)?;
    declare_leading_index_aux(d, p)?;
    declare_leading_index(d, p)?;
    declare_echelon_step_ok(d, p)?;
    declare_is_echelon_aux(d, p)?;
    declare_is_echelon(d, p)?;
    Ok(())
}

// --- small shapes ----------------------------------------------------------

/// `Bool.rec.{1}` selecting between two values of an arbitrary type `ty` —
/// [`bool_select_rat`] generalised, needed at `Nat`, `Bool` and the matrix
/// type.
pub(super) fn bool_select_at(
    d: &mut IntDev<'_>,
    ty: ExprId,
    condition: ExprId,
    on_true: ExprId,
    on_false: ExprId,
) -> ExprId {
    let bool_ty = d.bool_ty();
    let anon = d.anon_name();
    let motive = d.kernel().lam(anon, bool_ty, ty, BinderInfo::Default);
    let one = d.level_one();
    let bool_rec = d.int().logic.bool_rec;
    let rec = d.kernel().const_(bool_rec, vec![one]);
    d.apply(rec, &[motive, on_false, on_true, condition])
}

/// `Rat.inv x`.
pub(super) fn rinv(d: &mut IntDev<'_>, p: RatPrelude, x: ExprId) -> ExprId {
    d.const_app(p.inv, &[x])
}

/// `Rat.div x y`.
pub(super) fn rdiv(d: &mut IntDev<'_>, p: RatPrelude, x: ExprId, y: ExprId) -> ExprId {
    d.const_app(p.div, &[x, y])
}

/// `Rat.ble x y`.
fn rble(d: &mut IntDev<'_>, p: RatPrelude, x: ExprId, y: ExprId) -> ExprId {
    d.const_app(p.ble, &[x, y])
}

/// `Rat.isZeroB x`.
pub(super) fn ris_zero_b(d: &mut IntDev<'_>, p: RatPrelude, x: ExprId) -> ExprId {
    d.const_app(p.is_zero_b, &[x])
}

/// `Rat.matSetRow t h M`.
fn rset_row(d: &mut IntDev<'_>, p: RatPrelude, t: ExprId, h: ExprId, m: ExprId) -> ExprId {
    d.const_app(p.mat_set_row, &[t, h, m])
}

/// `Rat.rowSwap i j M`.
pub(super) fn rrow_swap(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    i: ExprId,
    j: ExprId,
    m: ExprId,
) -> ExprId {
    d.const_app(p.row_swap, &[i, j, m])
}

/// `Rat.rowScale i k M`.
pub(super) fn rrow_scale(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    i: ExprId,
    k: ExprId,
    m: ExprId,
) -> ExprId {
    d.const_app(p.row_scale, &[i, k, m])
}

/// `Rat.rowAddMul i j k M`.
pub(super) fn rrow_add_mul(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    i: ExprId,
    j: ExprId,
    k: ExprId,
    m: ExprId,
) -> ExprId {
    d.const_app(p.row_add_mul, &[i, j, k, m])
}

/// `Rat.pivotSearch M c start rows`.
pub(super) fn rpivot_search(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    m: ExprId,
    c: ExprId,
    start: ExprId,
    rows: ExprId,
) -> ExprId {
    d.const_app(p.pivot_search, &[m, c, start, rows])
}

/// `Rat.clearBelow M pr pc rows`.
pub(super) fn rclear_below(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    m: ExprId,
    pr: ExprId,
    pc: ExprId,
    rows: ExprId,
) -> ExprId {
    d.const_app(p.clear_below, &[m, pr, pc, rows])
}

/// `Rat.rowEchelon M rows cols`.
#[cfg(test)]
pub(super) fn rrow_echelon(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    m: ExprId,
    rows: ExprId,
    cols: ExprId,
) -> ExprId {
    d.const_app(p.row_echelon, &[m, rows, cols])
}

/// `Rat.leadingIndex M r cols`.
pub(super) fn rleading_index(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    m: ExprId,
    r: ExprId,
    cols: ExprId,
) -> ExprId {
    d.const_app(p.leading_index, &[m, r, cols])
}

/// `Rat.isEchelon M rows cols`.
#[cfg(test)]
pub(super) fn ris_echelon(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    m: ExprId,
    rows: ExprId,
    cols: ExprId,
) -> ExprId {
    d.const_app(p.is_echelon, &[m, rows, cols])
}

/// `Eq Bool (Nat.beq a b) Bool.false`.
fn beq_false_ty(d: &mut IntDev<'_>, a: ExprId, b: ExprId) -> ExprId {
    let lhs = NatOps::beq(d, a, b);
    let false_v = d.bool_false();
    d.bool_eq(lhs, false_v)
}

// --- the decided zero test -------------------------------------------------

/// Admit `Rat.isZeroB : Rat -> Bool`, `isZeroB x := if ble x 0 then ble 0 x
/// else false`.
fn declare_is_zero_b(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let carrier = rat_ty(d);
    let bool_ty = d.bool_ty();

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let zero = rzero(d, p);
    let upper = rble(d, p, x, zero);
    let lower = rble(d, p, zero, x);
    let false_v = d.bool_false();
    let body = bool_select_at(d, bool_ty, upper, lower, false_v);

    let value = d.lam_fv(x_fv, carrier, body);
    let ty = d.arrow(carrier, bool_ty);
    d.kernel().add_declaration(Declaration::Definition {
        name: p.is_zero_b,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(LEAF_HEIGHT),
    })
}

// --- the three elementary row operations -----------------------------------

/// Admit `Rat.rowSwap : Nat -> Nat -> Mat -> Mat`,
/// `rowSwap i j M := matSetRow i (M j) (matSetRow j (M i) M)`.
///
/// Both rows `M i` and `M j` are read off the ORIGINAL `M`, so the outer write
/// is not reading what the inner one just stored and the definition is a
/// genuine exchange rather than a copy.
fn declare_row_swap(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let mty = mat_ty(d);

    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);

    let row_i = d.apply(m, &[i]);
    let row_j = d.apply(m, &[j]);
    let inner = rset_row(d, p, j, row_i, m);
    let body = rset_row(d, p, i, row_j, inner);

    let value = {
        let over_m = d.lam_fv(m_fv, mty, body);
        let over_j = d.lam_fv(j_fv, nat, over_m);
        d.lam_fv(i_fv, nat, over_j)
    };
    let ty = {
        let over_m = d.arrow(mty, mty);
        let over_j = d.arrow(nat, over_m);
        d.arrow(nat, over_j)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.row_swap,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(ROW_OP_HEIGHT),
    })
}

/// Admit `Rat.rowScale : Nat -> Rat -> Mat -> Mat`,
/// `rowScale i k M := matSetRow i (fun c => k * M i c) M`.
fn declare_row_scale(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let mty = mat_ty(d);
    let carrier = rat_ty(d);

    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);

    let row = {
        let c_fv = d.fresh_fvar();
        let c = d.kernel().fvar(c_fv);
        let entry = d.apply(m, &[i, c]);
        let scaled = rmul(d, k, entry);
        d.lam_fv(c_fv, nat, scaled)
    };
    let body = rset_row(d, p, i, row, m);

    let value = {
        let over_m = d.lam_fv(m_fv, mty, body);
        let over_k = d.lam_fv(k_fv, carrier, over_m);
        d.lam_fv(i_fv, nat, over_k)
    };
    let ty = {
        let over_m = d.arrow(mty, mty);
        let over_k = d.arrow(carrier, over_m);
        d.arrow(nat, over_k)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.row_scale,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(ROW_OP_HEIGHT),
    })
}

/// Admit `Rat.rowAddMul : Nat -> Nat -> Rat -> Mat -> Mat`,
/// `rowAddMul i j k M := matSetRow i (fun c => M i c + k * M j c) M`.
fn declare_row_add_mul(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let mty = mat_ty(d);
    let carrier = rat_ty(d);

    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);

    let row = {
        let c_fv = d.fresh_fvar();
        let c = d.kernel().fvar(c_fv);
        let here = d.apply(m, &[i, c]);
        let there = d.apply(m, &[j, c]);
        let scaled = rmul(d, k, there);
        let sum = radd(d, here, scaled);
        d.lam_fv(c_fv, nat, sum)
    };
    let body = rset_row(d, p, i, row, m);

    let value = {
        let over_m = d.lam_fv(m_fv, mty, body);
        let over_k = d.lam_fv(k_fv, carrier, over_m);
        let over_j = d.lam_fv(j_fv, nat, over_k);
        d.lam_fv(i_fv, nat, over_j)
    };
    let ty = {
        let over_m = d.arrow(mty, mty);
        let over_k = d.arrow(carrier, over_m);
        let over_j = d.arrow(nat, over_k);
        d.arrow(nat, over_j)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.row_add_mul,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(ROW_OP_HEIGHT),
    })
}

// --- the row operations' equation lemmas -----------------------------------

/// Admit `Rat.rowSwap_at_left : ∀ i j M c, rowSwap i j M i c = M j c`.
///
/// One `Rat.matSetRow_at`: row `i` is the OUTER write, so no side condition
/// relating `i` and `j` is needed. This is the equation that stays true when
/// `i = j`, and it is what makes [`declare_row_swap_involutive`]'s degenerate
/// corner reachable at all.
fn declare_row_swap_at_left(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let mty = mat_ty(d);

    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);

    let swapped = rrow_swap(d, p, i, j, m);
    let lhs = d.apply(swapped, &[i, c]);
    let rhs = d.apply(m, &[j, c]);
    let stmt = req(d, lhs, rhs);

    let row_i = d.apply(m, &[i]);
    let row_j = d.apply(m, &[j]);
    let inner = rset_row(d, p, j, row_i, m);
    let proof = d.lemma(p.mat_set_row_at, &[i, row_j, inner, c]);

    let ty = {
        let over_c = d.pi_fv(c_fv, nat, stmt);
        let over_m = d.pi_fv(m_fv, mty, over_c);
        let over_j = d.pi_fv(j_fv, nat, over_m);
        d.pi_fv(i_fv, nat, over_j)
    };
    let value = {
        let over_c = d.lam_fv(c_fv, nat, proof);
        let over_m = d.lam_fv(m_fv, mty, over_c);
        let over_j = d.lam_fv(j_fv, nat, over_m);
        d.lam_fv(i_fv, nat, over_j)
    };
    d.declare_theorem(p.row_swap_at_left, ty, value)
}

/// Admit `Rat.rowSwap_at_right : ∀ i j M, Nat.beq j i = false → ∀ c,
/// rowSwap i j M j c = M i c`.
///
/// Row `j` is the INNER write, so reading it has to step past the outer one —
/// and that step is exactly where `j ≠ i` is required. The hypothesis is
/// written `Nat.beq j i` rather than `Nat.beq i j` because that is the
/// orientation `Rat.matSetRow_off` consumes (`beq r t`, row then target).
fn declare_row_swap_at_right(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let mty = mat_ty(d);

    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);

    let hyp_ty = beq_false_ty(d, j, i);

    let swapped = rrow_swap(d, p, i, j, m);
    let lhs = d.apply(swapped, &[j, c]);
    let rhs = d.apply(m, &[i, c]);
    let stmt = req(d, lhs, rhs);

    let row_i = d.apply(m, &[i]);
    let row_j = d.apply(m, &[j]);
    let inner = rset_row(d, p, j, row_i, m);
    // `matSetRow i (M j) inner j c = inner j c`, then `inner j c = (M i) c`.
    let step_off = d.lemma(p.mat_set_row_off, &[i, row_j, inner, j, h, c]);
    let step_at = d.lemma(p.mat_set_row_at, &[j, row_i, m, c]);
    let mid = d.apply(inner, &[j, c]);
    let proof = rtrans(d, lhs, mid, rhs, step_off, step_at);

    let ty = {
        let over_c = d.pi_fv(c_fv, nat, stmt);
        let over_h = d.pi_fv(h_fv, hyp_ty, over_c);
        let over_m = d.pi_fv(m_fv, mty, over_h);
        let over_j = d.pi_fv(j_fv, nat, over_m);
        d.pi_fv(i_fv, nat, over_j)
    };
    let value = {
        let over_c = d.lam_fv(c_fv, nat, proof);
        let over_h = d.lam_fv(h_fv, hyp_ty, over_c);
        let over_m = d.lam_fv(m_fv, mty, over_h);
        let over_j = d.lam_fv(j_fv, nat, over_m);
        d.lam_fv(i_fv, nat, over_j)
    };
    d.declare_theorem(p.row_swap_at_right, ty, value)
}

/// Admit `Rat.rowSwap_off : ∀ i j M r, Nat.beq r i = false →
/// Nat.beq r j = false → ∀ c, rowSwap i j M r c = M r c`.
fn declare_row_swap_off(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let mty = mat_ty(d);

    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let r_fv = d.fresh_fvar();
    let r = d.kernel().fvar(r_fv);
    let hi_fv = d.fresh_fvar();
    let hi = d.kernel().fvar(hi_fv);
    let hj_fv = d.fresh_fvar();
    let hj = d.kernel().fvar(hj_fv);
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);

    let hi_ty = beq_false_ty(d, r, i);
    let hj_ty = beq_false_ty(d, r, j);

    let swapped = rrow_swap(d, p, i, j, m);
    let lhs = d.apply(swapped, &[r, c]);
    let rhs = d.apply(m, &[r, c]);
    let stmt = req(d, lhs, rhs);

    let row_i = d.apply(m, &[i]);
    let row_j = d.apply(m, &[j]);
    let inner = rset_row(d, p, j, row_i, m);
    let step_outer = d.lemma(p.mat_set_row_off, &[i, row_j, inner, r, hi, c]);
    let step_inner = d.lemma(p.mat_set_row_off, &[j, row_i, m, r, hj, c]);
    let mid = d.apply(inner, &[r, c]);
    let proof = rtrans(d, lhs, mid, rhs, step_outer, step_inner);

    let ty = {
        let over_c = d.pi_fv(c_fv, nat, stmt);
        let over_hj = d.pi_fv(hj_fv, hj_ty, over_c);
        let over_hi = d.pi_fv(hi_fv, hi_ty, over_hj);
        let over_r = d.pi_fv(r_fv, nat, over_hi);
        let over_m = d.pi_fv(m_fv, mty, over_r);
        let over_j = d.pi_fv(j_fv, nat, over_m);
        d.pi_fv(i_fv, nat, over_j)
    };
    let value = {
        let over_c = d.lam_fv(c_fv, nat, proof);
        let over_hj = d.lam_fv(hj_fv, hj_ty, over_c);
        let over_hi = d.lam_fv(hi_fv, hi_ty, over_hj);
        let over_r = d.lam_fv(r_fv, nat, over_hi);
        let over_m = d.lam_fv(m_fv, mty, over_r);
        let over_j = d.lam_fv(j_fv, nat, over_m);
        d.lam_fv(i_fv, nat, over_j)
    };
    d.declare_theorem(p.row_swap_off, ty, value)
}

/// Admit `Rat.rowScale_at : ∀ i k M c, rowScale i k M i c = k * M i c`.
fn declare_row_scale_at(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let mty = mat_ty(d);
    let carrier = rat_ty(d);

    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);

    let scaled_mat = rrow_scale(d, p, i, k, m);
    let lhs = d.apply(scaled_mat, &[i, c]);
    let entry = d.apply(m, &[i, c]);
    let rhs = rmul(d, k, entry);
    let stmt = req(d, lhs, rhs);

    let row = scale_row_fn(d, i, k, m);
    let proof = d.lemma(p.mat_set_row_at, &[i, row, m, c]);

    let ty = {
        let over_c = d.pi_fv(c_fv, nat, stmt);
        let over_m = d.pi_fv(m_fv, mty, over_c);
        let over_k = d.pi_fv(k_fv, carrier, over_m);
        d.pi_fv(i_fv, nat, over_k)
    };
    let value = {
        let over_c = d.lam_fv(c_fv, nat, proof);
        let over_m = d.lam_fv(m_fv, mty, over_c);
        let over_k = d.lam_fv(k_fv, carrier, over_m);
        d.lam_fv(i_fv, nat, over_k)
    };
    d.declare_theorem(p.row_scale_at, ty, value)
}

/// `fun c => k * M i c` — the row [`declare_row_scale`] writes, rebuilt so the
/// equation lemmas can name it.
fn scale_row_fn(d: &mut IntDev<'_>, i: ExprId, k: ExprId, m: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let entry = d.apply(m, &[i, c]);
    let scaled = rmul(d, k, entry);
    d.lam_fv(c_fv, nat, scaled)
}

/// `fun c => M i c + k * M j c` — the row [`declare_row_add_mul`] writes.
fn add_mul_row_fn(d: &mut IntDev<'_>, i: ExprId, j: ExprId, k: ExprId, m: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let here = d.apply(m, &[i, c]);
    let there = d.apply(m, &[j, c]);
    let scaled = rmul(d, k, there);
    let sum = radd(d, here, scaled);
    d.lam_fv(c_fv, nat, sum)
}

/// Admit `Rat.rowScale_off : ∀ i k M r, Nat.beq r i = false → ∀ c,
/// rowScale i k M r c = M r c`.
fn declare_row_scale_off(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let mty = mat_ty(d);
    let carrier = rat_ty(d);

    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let r_fv = d.fresh_fvar();
    let r = d.kernel().fvar(r_fv);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);

    let hyp_ty = beq_false_ty(d, r, i);
    let scaled_mat = rrow_scale(d, p, i, k, m);
    let lhs = d.apply(scaled_mat, &[r, c]);
    let rhs = d.apply(m, &[r, c]);
    let stmt = req(d, lhs, rhs);

    let row = scale_row_fn(d, i, k, m);
    let proof = d.lemma(p.mat_set_row_off, &[i, row, m, r, h, c]);

    let ty = {
        let over_c = d.pi_fv(c_fv, nat, stmt);
        let over_h = d.pi_fv(h_fv, hyp_ty, over_c);
        let over_r = d.pi_fv(r_fv, nat, over_h);
        let over_m = d.pi_fv(m_fv, mty, over_r);
        let over_k = d.pi_fv(k_fv, carrier, over_m);
        d.pi_fv(i_fv, nat, over_k)
    };
    let value = {
        let over_c = d.lam_fv(c_fv, nat, proof);
        let over_h = d.lam_fv(h_fv, hyp_ty, over_c);
        let over_r = d.lam_fv(r_fv, nat, over_h);
        let over_m = d.lam_fv(m_fv, mty, over_r);
        let over_k = d.lam_fv(k_fv, carrier, over_m);
        d.lam_fv(i_fv, nat, over_k)
    };
    d.declare_theorem(p.row_scale_off, ty, value)
}

/// Admit `Rat.rowAddMul_at : ∀ i j k M c,
/// rowAddMul i j k M i c = M i c + k * M j c`.
fn declare_row_add_mul_at(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let mty = mat_ty(d);
    let carrier = rat_ty(d);

    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);

    let combined = rrow_add_mul(d, p, i, j, k, m);
    let lhs = d.apply(combined, &[i, c]);
    let here = d.apply(m, &[i, c]);
    let there = d.apply(m, &[j, c]);
    let scaled = rmul(d, k, there);
    let rhs = radd(d, here, scaled);
    let stmt = req(d, lhs, rhs);

    let row = add_mul_row_fn(d, i, j, k, m);
    let proof = d.lemma(p.mat_set_row_at, &[i, row, m, c]);

    let ty = {
        let over_c = d.pi_fv(c_fv, nat, stmt);
        let over_m = d.pi_fv(m_fv, mty, over_c);
        let over_k = d.pi_fv(k_fv, carrier, over_m);
        let over_j = d.pi_fv(j_fv, nat, over_k);
        d.pi_fv(i_fv, nat, over_j)
    };
    let value = {
        let over_c = d.lam_fv(c_fv, nat, proof);
        let over_m = d.lam_fv(m_fv, mty, over_c);
        let over_k = d.lam_fv(k_fv, carrier, over_m);
        let over_j = d.lam_fv(j_fv, nat, over_k);
        d.lam_fv(i_fv, nat, over_j)
    };
    d.declare_theorem(p.row_add_mul_at, ty, value)
}

/// Admit `Rat.rowAddMul_off : ∀ i j k M r, Nat.beq r i = false → ∀ c,
/// rowAddMul i j k M r c = M r c`.
fn declare_row_add_mul_off(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let mty = mat_ty(d);
    let carrier = rat_ty(d);

    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let r_fv = d.fresh_fvar();
    let r = d.kernel().fvar(r_fv);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);

    let hyp_ty = beq_false_ty(d, r, i);
    let combined = rrow_add_mul(d, p, i, j, k, m);
    let lhs = d.apply(combined, &[r, c]);
    let rhs = d.apply(m, &[r, c]);
    let stmt = req(d, lhs, rhs);

    let row = add_mul_row_fn(d, i, j, k, m);
    let proof = d.lemma(p.mat_set_row_off, &[i, row, m, r, h, c]);

    let ty = {
        let over_c = d.pi_fv(c_fv, nat, stmt);
        let over_h = d.pi_fv(h_fv, hyp_ty, over_c);
        let over_r = d.pi_fv(r_fv, nat, over_h);
        let over_m = d.pi_fv(m_fv, mty, over_r);
        let over_k = d.pi_fv(k_fv, carrier, over_m);
        let over_j = d.pi_fv(j_fv, nat, over_k);
        d.pi_fv(i_fv, nat, over_j)
    };
    let value = {
        let over_c = d.lam_fv(c_fv, nat, proof);
        let over_h = d.lam_fv(h_fv, hyp_ty, over_c);
        let over_r = d.lam_fv(r_fv, nat, over_h);
        let over_m = d.lam_fv(m_fv, mty, over_r);
        let over_k = d.lam_fv(k_fv, carrier, over_m);
        let over_j = d.lam_fv(j_fv, nat, over_k);
        d.lam_fv(i_fv, nat, over_j)
    };
    d.declare_theorem(p.row_add_mul_off, ty, value)
}

// --- each row operation has a kernel-checked inverse -----------------------

/// From `h : Nat.beq a b = Bool.true`, the equation `Eq Nat a b`.
fn eq_of_beq_true(d: &mut IntDev<'_>, a: ExprId, b: ExprId, h: ExprId) -> ExprId {
    let np = d.prelude();
    d.lemma(np.eq_of_beq_eq_true, &[a, b, h])
}

/// Admit `Rat.rowSwap_involutive : ∀ i j M r c,
/// rowSwap i j (rowSwap i j M) r c = M r c`.
///
/// **Unconditional — `i = j` included, and that corner is not free.** At
/// `r = i` the outer write reads row `j` of the once-swapped matrix, and which
/// `Rat.matSetRow` equation applies to that read depends on whether `j = i`.
/// So the proof is a `Nat.beq r i` split with a second `Nat.beq j i` split
/// inside its `true` branch and a `Nat.beq r j` split inside its `false` one;
/// three of the four leaves are two chained equation lemmas and the fourth is
/// a transport of the row index.
///
/// This is what makes a swap a bijection on matrices, which is the property
/// rank invariance consumes.
fn declare_row_swap_involutive(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let mty = mat_ty(d);

    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let r_fv = d.fresh_fvar();
    let r = d.kernel().fvar(r_fv);
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);

    let once = rrow_swap(d, p, i, j, m);
    let twice = rrow_swap(d, p, i, j, once);

    // `fun x => Eq Rat (rowSwap i j (rowSwap i j M) x c) (M x c)`, the shape
    // both transports move along.
    let goal_at = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let lhs = d.apply(twice, &[x, c]);
        let rhs = d.apply(m, &[x, c]);
        req(d, lhs, rhs)
    };
    let stmt = goal_at(d, r);

    // --- r = i: the outer write hands back row `j` of the once-swapped matrix.
    let at_true = {
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let true_v = d.bool_true();
        let cond = NatOps::beq(d, r, i);
        let h_ty = d.bool_eq(cond, true_v);

        let he = eq_of_beq_true(d, r, i, h);

        // `rowSwap i j once i c = once j c`.
        let step_a = d.lemma(p.row_swap_at_left, &[i, j, once, c]);
        let mid = d.apply(once, &[j, c]);
        let target_b = {
            let rhs = d.apply(m, &[i, c]);
            req(d, mid, rhs)
        };

        // `once j c = M i c`, by cases on whether `j = i`.
        let inner_true = {
            let g_fv = d.fresh_fvar();
            let g = d.kernel().fvar(g_fv);
            let cond_ji = NatOps::beq(d, j, i);
            let g_ty = d.bool_eq(cond_ji, true_v);

            let hje = eq_of_beq_true(d, j, i, g);
            // `rowSwap i j M i c = M j c = M i c`.
            let pf1 = d.lemma(p.row_swap_at_left, &[i, j, m, c]);
            let pf2 = nat_eq_to_rat(d, j, i, hje, &|d, x| d.apply(m, &[x, c]));
            let a0 = d.apply(once, &[i, c]);
            let a1 = d.apply(m, &[j, c]);
            let a2 = d.apply(m, &[i, c]);
            let at_i = rtrans(d, a0, a1, a2, pf1, pf2);
            // transport the ROW index `i` to `j`.
            let symm_hje = NatOps::symm(d, j, i, hje);
            let body = nat_rewrite_prop(d, i, j, symm_hje, at_i, &|d, x| {
                let lhs = d.apply(once, &[x, c]);
                let rhs = d.apply(m, &[i, c]);
                req(d, lhs, rhs)
            });
            d.lam_fv(g_fv, g_ty, body)
        };
        let inner_false = {
            let g_fv = d.fresh_fvar();
            let g = d.kernel().fvar(g_fv);
            let cond_ji = NatOps::beq(d, j, i);
            let false_v = d.bool_false();
            let g_ty = d.bool_eq(cond_ji, false_v);
            let body = d.lemma(p.row_swap_at_right, &[i, j, m, g, c]);
            d.lam_fv(g_fv, g_ty, body)
        };
        let cond_ji = NatOps::beq(d, j, i);
        let step_b = bool_cases_eq(d, cond_ji, target_b, inner_true, inner_false);

        let start = d.apply(twice, &[i, c]);
        let end = d.apply(m, &[i, c]);
        let at_i = rtrans(d, start, mid, end, step_a, step_b);

        let symm_he = NatOps::symm(d, r, i, he);
        let body = nat_rewrite_prop(d, i, r, symm_he, at_i, &goal_at);
        d.lam_fv(h_fv, h_ty, body)
    };

    // --- r ≠ i: either `r` is untouched by both writes, or `r = j`.
    let at_false = {
        let hi_fv = d.fresh_fvar();
        let hi = d.kernel().fvar(hi_fv);
        let hi_ty = beq_false_ty(d, r, i);

        let inner_true = {
            let g_fv = d.fresh_fvar();
            let g = d.kernel().fvar(g_fv);
            let cond_rj = NatOps::beq(d, r, j);
            let true_v = d.bool_true();
            let g_ty = d.bool_eq(cond_rj, true_v);

            let hrj = eq_of_beq_true(d, r, j, g);
            // `beq j i = false`, moved along `r = j`.
            let hji = nat_rewrite_prop(d, r, j, hrj, hi, &|d, x| beq_false_ty(d, x, i));
            let pf1 = d.lemma(p.row_swap_at_right, &[i, j, once, hji, c]);
            let pf2 = d.lemma(p.row_swap_at_left, &[i, j, m, c]);
            let a0 = d.apply(twice, &[j, c]);
            let a1 = d.apply(once, &[i, c]);
            let a2 = d.apply(m, &[j, c]);
            let at_j = rtrans(d, a0, a1, a2, pf1, pf2);
            let symm_hrj = NatOps::symm(d, r, j, hrj);
            let body = nat_rewrite_prop(d, j, r, symm_hrj, at_j, &goal_at);
            d.lam_fv(g_fv, g_ty, body)
        };
        let inner_false = {
            let g_fv = d.fresh_fvar();
            let g = d.kernel().fvar(g_fv);
            let g_ty = beq_false_ty(d, r, j);
            let pf1 = d.lemma(p.row_swap_off, &[i, j, once, r, hi, g, c]);
            let pf2 = d.lemma(p.row_swap_off, &[i, j, m, r, hi, g, c]);
            let a0 = d.apply(twice, &[r, c]);
            let a1 = d.apply(once, &[r, c]);
            let a2 = d.apply(m, &[r, c]);
            let body = rtrans(d, a0, a1, a2, pf1, pf2);
            d.lam_fv(g_fv, g_ty, body)
        };
        let cond_rj = NatOps::beq(d, r, j);
        let body = bool_cases_eq(d, cond_rj, stmt, inner_true, inner_false);
        d.lam_fv(hi_fv, hi_ty, body)
    };

    let cond_ri = NatOps::beq(d, r, i);
    let proof = bool_cases_eq(d, cond_ri, stmt, at_true, at_false);

    let ty = {
        let over_c = d.pi_fv(c_fv, nat, stmt);
        let over_r = d.pi_fv(r_fv, nat, over_c);
        let over_m = d.pi_fv(m_fv, mty, over_r);
        let over_j = d.pi_fv(j_fv, nat, over_m);
        d.pi_fv(i_fv, nat, over_j)
    };
    let value = {
        let over_c = d.lam_fv(c_fv, nat, proof);
        let over_r = d.lam_fv(r_fv, nat, over_c);
        let over_m = d.lam_fv(m_fv, mty, over_r);
        let over_j = d.lam_fv(j_fv, nat, over_m);
        d.lam_fv(i_fv, nat, over_j)
    };
    d.declare_theorem(p.row_swap_involutive, ty, value)
}

/// Admit `Rat.rowAddMul_inverse : ∀ i j k M, Nat.beq j i = false → ∀ r c,
/// rowAddMul i j (neg k) (rowAddMul i j k M) r c = M r c`.
///
/// `j ≠ i` is REQUIRED, not convenience: at `i = j` the operation scales row
/// `i` by `1 + k` and its inverse is a scaling by `1/(1+k)`, not an addition of
/// `-k`. The hypothesis also does real work inside the proof — it is what says
/// row `j` of the once-modified matrix still holds `M j`, which is the only
/// reason the two multiples cancel.
fn declare_row_add_mul_inverse(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let mty = mat_ty(d);
    let carrier = rat_ty(d);

    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);
    let r_fv = d.fresh_fvar();
    let r = d.kernel().fvar(r_fv);
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);

    let hyp_ty = beq_false_ty(d, j, i);
    let neg_k = rneg(d, k);
    let once = rrow_add_mul(d, p, i, j, k, m);
    let twice = rrow_add_mul(d, p, i, j, neg_k, once);

    let goal_at = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let lhs = d.apply(twice, &[x, c]);
        let rhs = d.apply(m, &[x, c]);
        req(d, lhs, rhs)
    };
    let stmt = goal_at(d, r);

    let at_true = {
        let g_fv = d.fresh_fvar();
        let g = d.kernel().fvar(g_fv);
        let cond = NatOps::beq(d, r, i);
        let true_v = d.bool_true();
        let g_ty = d.bool_eq(cond, true_v);
        let he = eq_of_beq_true(d, r, i, g);

        let a = d.apply(m, &[i, c]);
        let b = d.apply(m, &[j, c]);
        let big_a = d.apply(once, &[i, c]);
        let big_b = d.apply(once, &[j, c]);

        // `twice i c = once i c + (-k) * once j c`.
        let step0 = d.lemma(p.row_add_mul_at, &[i, j, neg_k, once, c]);
        let start = d.apply(twice, &[i, c]);
        let t0 = {
            let scaled = rmul(d, neg_k, big_b);
            radd(d, big_a, scaled)
        };

        // `once i c = a + k * b`.
        let pf_a = d.lemma(p.row_add_mul_at, &[i, j, k, m, c]);
        let kb = rmul(d, k, b);
        let a_plus_kb = radd(d, a, kb);
        let step1 = rcongr(d, big_a, a_plus_kb, pf_a, &|d, x| {
            let scaled = rmul(d, neg_k, big_b);
            radd(d, x, scaled)
        });
        let t1 = {
            let scaled = rmul(d, neg_k, big_b);
            radd(d, a_plus_kb, scaled)
        };

        // `once j c = b`, which is where `j ≠ i` is spent.
        let pf_b = d.lemma(p.row_add_mul_off, &[i, j, k, m, j, h, c]);
        let step2 = rcongr(d, big_b, b, pf_b, &|d, x| {
            let scaled = rmul(d, neg_k, x);
            radd(d, a_plus_kb, scaled)
        });
        let neg_k_b = rmul(d, neg_k, b);
        let t2 = radd(d, a_plus_kb, neg_k_b);

        // `(-k) * b = -(k * b)`.
        let neg_mul_pf = d.lemma(p.neg_mul, &[k, b]);
        let neg_kb = rneg(d, kb);
        let step3 = rcongr(d, neg_k_b, neg_kb, neg_mul_pf, &|d, x| {
            radd(d, a_plus_kb, x)
        });
        let t3 = radd(d, a_plus_kb, neg_kb);

        // `(a + k*b) + -(k*b) = a + (k*b + -(k*b))`.
        let step4 = d.lemma(p.add_assoc, &[a, kb, neg_kb]);
        let inner_sum = radd(d, kb, neg_kb);
        let t4 = radd(d, a, inner_sum);

        // `k*b + -(k*b) = 0`.
        let add_neg_pf = d.lemma(p.add_neg, &[kb]);
        let zero = rzero(d, p);
        let step5 = rcongr(d, inner_sum, zero, add_neg_pf, &|d, x| radd(d, a, x));
        let t5 = radd(d, a, zero);

        // `a + 0 = a`.
        let step6 = d.lemma(p.add_zero, &[a]);

        let (_, at_i) = rchain(
            d,
            start,
            &[
                (t0, step0),
                (t1, step1),
                (t2, step2),
                (t3, step3),
                (t4, step4),
                (t5, step5),
                (a, step6),
            ],
        );

        let symm_he = NatOps::symm(d, r, i, he);
        let body = nat_rewrite_prop(d, i, r, symm_he, at_i, &goal_at);
        d.lam_fv(g_fv, g_ty, body)
    };

    let at_false = {
        let g_fv = d.fresh_fvar();
        let g = d.kernel().fvar(g_fv);
        let g_ty = beq_false_ty(d, r, i);
        let pf1 = d.lemma(p.row_add_mul_off, &[i, j, neg_k, once, r, g, c]);
        let pf2 = d.lemma(p.row_add_mul_off, &[i, j, k, m, r, g, c]);
        let a0 = d.apply(twice, &[r, c]);
        let a1 = d.apply(once, &[r, c]);
        let a2 = d.apply(m, &[r, c]);
        let body = rtrans(d, a0, a1, a2, pf1, pf2);
        d.lam_fv(g_fv, g_ty, body)
    };

    let cond = NatOps::beq(d, r, i);
    let proof = bool_cases_eq(d, cond, stmt, at_true, at_false);

    let ty = {
        let over_c = d.pi_fv(c_fv, nat, stmt);
        let over_r = d.pi_fv(r_fv, nat, over_c);
        let over_h = d.pi_fv(h_fv, hyp_ty, over_r);
        let over_m = d.pi_fv(m_fv, mty, over_h);
        let over_k = d.pi_fv(k_fv, carrier, over_m);
        let over_j = d.pi_fv(j_fv, nat, over_k);
        d.pi_fv(i_fv, nat, over_j)
    };
    let value = {
        let over_c = d.lam_fv(c_fv, nat, proof);
        let over_r = d.lam_fv(r_fv, nat, over_c);
        let over_h = d.lam_fv(h_fv, hyp_ty, over_r);
        let over_m = d.lam_fv(m_fv, mty, over_h);
        let over_k = d.lam_fv(k_fv, carrier, over_m);
        let over_j = d.lam_fv(j_fv, nat, over_k);
        d.lam_fv(i_fv, nat, over_j)
    };
    d.declare_theorem(p.row_add_mul_inverse, ty, value)
}

/// Admit `Rat.rowScale_inverse : ∀ i k M, Not (Eq Rat k Rat.zero) → ∀ r c,
/// rowScale i (inv k) (rowScale i k M) r c = M r c`.
///
/// The hypothesis is `k ≠ 0` rather than `0 < k`, so it covers the negative
/// pivots row reduction actually produces; `Rat.mul_inv_cancel_of_ne_zero` is
/// the form that carries it. This prelude has no `one_mul`, so the last step
/// goes `1 * a = a * 1 = a` through `Rat.mul_comm` and `Rat.mul_one`.
fn declare_row_scale_inverse(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let mty = mat_ty(d);
    let carrier = rat_ty(d);

    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);
    let r_fv = d.fresh_fvar();
    let r = d.kernel().fvar(r_fv);
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);

    let zero = rzero(d, p);
    let k_eq_zero = req(d, k, zero);
    let logic = d.prelude().logic;
    let false_ty = d.kernel().const_(logic.false_, vec![]);
    let hyp_ty = d.arrow(k_eq_zero, false_ty);

    let inv_k = rinv(d, p, k);
    let once = rrow_scale(d, p, i, k, m);
    let twice = rrow_scale(d, p, i, inv_k, once);

    let goal_at = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let lhs = d.apply(twice, &[x, c]);
        let rhs = d.apply(m, &[x, c]);
        req(d, lhs, rhs)
    };
    let stmt = goal_at(d, r);

    let at_true = {
        let g_fv = d.fresh_fvar();
        let g = d.kernel().fvar(g_fv);
        let cond = NatOps::beq(d, r, i);
        let true_v = d.bool_true();
        let g_ty = d.bool_eq(cond, true_v);
        let he = eq_of_beq_true(d, r, i, g);

        let a = d.apply(m, &[i, c]);
        let big_a = d.apply(once, &[i, c]);

        // `twice i c = inv k * once i c`.
        let step0 = d.lemma(p.row_scale_at, &[i, inv_k, once, c]);
        let start = d.apply(twice, &[i, c]);
        let t0 = rmul(d, inv_k, big_a);

        // `once i c = k * a`.
        let pf_a = d.lemma(p.row_scale_at, &[i, k, m, c]);
        let ka = rmul(d, k, a);
        let step1 = rcongr(d, big_a, ka, pf_a, &|d, x| rmul(d, inv_k, x));
        let t1 = rmul(d, inv_k, ka);

        // `(inv k * k) * a = inv k * (k * a)`, used right to left.
        let inv_times_k = rmul(d, inv_k, k);
        let assoc = d.lemma(p.mul_assoc, &[inv_k, k, a]);
        let t2 = rmul(d, inv_times_k, a);
        let step2 = rsymm(d, t2, t1, assoc);

        // `inv k * k = k * inv k = 1`.
        let comm = d.lemma(p.mul_comm, &[inv_k, k]);
        let k_times_inv = rmul(d, k, inv_k);
        let one = rone(d, p);
        let cancel = d.lemma(p.mul_inv_cancel_of_ne_zero, &[k, h]);
        let to_one = rtrans(d, inv_times_k, k_times_inv, one, comm, cancel);
        let step3 = rcongr(d, inv_times_k, one, to_one, &|d, x| rmul(d, x, a));
        let t3 = rmul(d, one, a);

        // `1 * a = a * 1 = a`.
        let comm_one = d.lemma(p.mul_comm, &[one, a]);
        let a_times_one = rmul(d, a, one);
        let mul_one_pf = d.lemma(p.mul_one, &[a]);
        let step4 = rtrans(d, t3, a_times_one, a, comm_one, mul_one_pf);

        let (_, at_i) = rchain(
            d,
            start,
            &[
                (t0, step0),
                (t1, step1),
                (t2, step2),
                (t3, step3),
                (a, step4),
            ],
        );

        let symm_he = NatOps::symm(d, r, i, he);
        let body = nat_rewrite_prop(d, i, r, symm_he, at_i, &goal_at);
        d.lam_fv(g_fv, g_ty, body)
    };

    let at_false = {
        let g_fv = d.fresh_fvar();
        let g = d.kernel().fvar(g_fv);
        let g_ty = beq_false_ty(d, r, i);
        let pf1 = d.lemma(p.row_scale_off, &[i, inv_k, once, r, g, c]);
        let pf2 = d.lemma(p.row_scale_off, &[i, k, m, r, g, c]);
        let a0 = d.apply(twice, &[r, c]);
        let a1 = d.apply(once, &[r, c]);
        let a2 = d.apply(m, &[r, c]);
        let body = rtrans(d, a0, a1, a2, pf1, pf2);
        d.lam_fv(g_fv, g_ty, body)
    };

    let cond = NatOps::beq(d, r, i);
    let proof = bool_cases_eq(d, cond, stmt, at_true, at_false);

    let ty = {
        let over_c = d.pi_fv(c_fv, nat, stmt);
        let over_r = d.pi_fv(r_fv, nat, over_c);
        let over_h = d.pi_fv(h_fv, hyp_ty, over_r);
        let over_m = d.pi_fv(m_fv, mty, over_h);
        let over_k = d.pi_fv(k_fv, carrier, over_m);
        d.pi_fv(i_fv, nat, over_k)
    };
    let value = {
        let over_c = d.lam_fv(c_fv, nat, proof);
        let over_r = d.lam_fv(r_fv, nat, over_c);
        let over_h = d.lam_fv(h_fv, hyp_ty, over_r);
        let over_m = d.lam_fv(m_fv, mty, over_h);
        let over_k = d.lam_fv(k_fv, carrier, over_m);
        d.lam_fv(i_fv, nat, over_k)
    };
    d.declare_theorem(p.row_scale_inverse, ty, value)
}

// --- the computed searches and the elimination loop ------------------------

/// `Nat.rec.{1}` at a motive constant in the recursion variable — the fuel
/// idiom every definition below uses.
pub(super) fn nat_fuel_rec(
    d: &mut IntDev<'_>,
    inner_ty: ExprId,
    zero_case: ExprId,
    succ_case: ExprId,
    fuel: ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let anon = d.anon_name();
    let motive = d.kernel().lam(anon, nat, inner_ty, BinderInfo::Default);
    let one = d.level_one();
    let rec_name = d.prelude().rec;
    let rec = d.kernel().const_(rec_name, vec![one]);
    d.apply(rec, &[motive, zero_case, succ_case, fuel])
}

/// Admit `Rat.pivotSearchAux : Mat -> Nat -> Nat -> Nat -> Nat -> Nat`,
/// `pivotSearchAux M c rows fuel r`.
///
/// Returns the first `r' >= r` below `rows` whose column-`c` entry is nonzero,
/// and `rows` when the fuel runs out or the scan reaches the bound. Both
/// exhaustion answers are the SAME value on purpose: `rows` is out of range, so
/// a caller reads "no pivot here" from one test and does not have to
/// distinguish "searched everything" from "gave up".
fn declare_pivot_search_aux(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let mty = mat_ty(d);

    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let rows_fv = d.fresh_fvar();
    let rows = d.kernel().fvar(rows_fv);

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

        let entry = d.apply(m, &[r, c]);
        let is_zero = ris_zero_b(d, p, entry);
        let sr = d.succ(r);
        let recurse = d.apply(ih, &[sr]);
        let keep_looking = bool_select_at(d, nat, is_zero, recurse, r);
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
        let over_rows = d.lam_fv(rows_fv, nat, over_fuel);
        let over_c = d.lam_fv(c_fv, nat, over_rows);
        d.lam_fv(m_fv, mty, over_c)
    };
    let ty = {
        let over_r = d.arrow(nat, nat);
        let over_fuel = d.arrow(nat, over_r);
        let over_rows = d.arrow(nat, over_fuel);
        let over_c = d.arrow(nat, over_rows);
        d.arrow(mty, over_c)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.pivot_search_aux,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(SEARCH_AUX_HEIGHT),
    })
}

/// Admit `Rat.pivotSearch : Mat -> Nat -> Nat -> Nat -> Nat`,
/// `pivotSearch M c start rows := pivotSearchAux M c rows rows start`.
///
/// Fuel `rows` is sufficient because the scan starts at `start >= 0` and stops
/// at `rows`.
fn declare_pivot_search(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
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

    let body = d.const_app(p.pivot_search_aux, &[m, c, rows, rows, start]);
    let value = {
        let over_rows = d.lam_fv(rows_fv, nat, body);
        let over_start = d.lam_fv(start_fv, nat, over_rows);
        let over_c = d.lam_fv(c_fv, nat, over_start);
        d.lam_fv(m_fv, mty, over_c)
    };
    let ty = {
        let over_rows = d.arrow(nat, nat);
        let over_start = d.arrow(nat, over_rows);
        let over_c = d.arrow(nat, over_start);
        d.arrow(mty, over_c)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.pivot_search,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(SWEEP_HEIGHT),
    })
}

/// Admit `Rat.clearBelowAux : Nat -> Nat -> Nat -> Nat -> Mat -> Nat -> Mat`,
/// `clearBelowAux pr pc rows fuel M r`.
///
/// Subtracts `(M r pc / M pr pc)` times the pivot row from row `r`, then moves
/// on. The matrix travels INSIDE the recursion because each step rewrites it;
/// `pr`, `pc` and `rows` are fixed and sit outside.
fn declare_clear_below_aux(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let mty = mat_ty(d);

    let pr_fv = d.fresh_fvar();
    let pr = d.kernel().fvar(pr_fv);
    let pc_fv = d.fresh_fvar();
    let pc = d.kernel().fvar(pc_fv);
    let rows_fv = d.fresh_fvar();
    let rows = d.kernel().fvar(rows_fv);

    let inner_ty = {
        let over_r = d.arrow(nat, mty);
        d.arrow(mty, over_r)
    };

    let zero_case = {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let r_fv = d.fresh_fvar();
        let over_r = d.lam_fv(r_fv, nat, m);
        d.lam_fv(m_fv, mty, over_r)
    };
    let succ_case = {
        let n_fv = d.fresh_fvar();
        let ih_fv = d.fresh_fvar();
        let ih = d.kernel().fvar(ih_fv);
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);

        let here = d.apply(m, &[r, pc]);
        let pivot = d.apply(m, &[pr, pc]);
        let ratio = rdiv(d, p, here, pivot);
        let factor = rneg(d, ratio);
        let updated = rrow_add_mul(d, p, r, pr, factor, m);
        let sr = d.succ(r);
        let recurse = d.apply(ih, &[updated, sr]);
        let out_of_range = NatOps::ble(d, rows, r);
        let body = bool_select_at(d, mty, out_of_range, m, recurse);

        let over_r = d.lam_fv(r_fv, nat, body);
        let over_m = d.lam_fv(m_fv, mty, over_r);
        let over_ih = d.lam_fv(ih_fv, inner_ty, over_m);
        d.lam_fv(n_fv, nat, over_ih)
    };

    let fuel_fv = d.fresh_fvar();
    let fuel = d.kernel().fvar(fuel_fv);
    let rec_app = nat_fuel_rec(d, inner_ty, zero_case, succ_case, fuel);
    let m_outer_fv = d.fresh_fvar();
    let m_outer = d.kernel().fvar(m_outer_fv);
    let r_outer_fv = d.fresh_fvar();
    let r_outer = d.kernel().fvar(r_outer_fv);
    let applied = d.apply(rec_app, &[m_outer, r_outer]);

    let value = {
        let over_r = d.lam_fv(r_outer_fv, nat, applied);
        let over_m = d.lam_fv(m_outer_fv, mty, over_r);
        let over_fuel = d.lam_fv(fuel_fv, nat, over_m);
        let over_rows = d.lam_fv(rows_fv, nat, over_fuel);
        let over_pc = d.lam_fv(pc_fv, nat, over_rows);
        d.lam_fv(pr_fv, nat, over_pc)
    };
    let ty = {
        let over_r = d.arrow(nat, mty);
        let over_m = d.arrow(mty, over_r);
        let over_fuel = d.arrow(nat, over_m);
        let over_rows = d.arrow(nat, over_fuel);
        let over_pc = d.arrow(nat, over_rows);
        d.arrow(nat, over_pc)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.clear_below_aux,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(SWEEP_HEIGHT),
    })
}

/// Admit `Rat.clearBelow : Mat -> Nat -> Nat -> Nat -> Mat`,
/// `clearBelow M pr pc rows := clearBelowAux pr pc rows rows M (succ pr)`.
fn declare_clear_below(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let mty = mat_ty(d);

    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let pr_fv = d.fresh_fvar();
    let pr = d.kernel().fvar(pr_fv);
    let pc_fv = d.fresh_fvar();
    let pc = d.kernel().fvar(pc_fv);
    let rows_fv = d.fresh_fvar();
    let rows = d.kernel().fvar(rows_fv);

    let spr = d.succ(pr);
    let body = d.const_app(p.clear_below_aux, &[pr, pc, rows, rows, m, spr]);
    let value = {
        let over_rows = d.lam_fv(rows_fv, nat, body);
        let over_pc = d.lam_fv(pc_fv, nat, over_rows);
        let over_pr = d.lam_fv(pr_fv, nat, over_pc);
        d.lam_fv(m_fv, mty, over_pr)
    };
    let ty = {
        let over_rows = d.arrow(nat, mty);
        let over_pc = d.arrow(nat, over_rows);
        let over_pr = d.arrow(nat, over_pc);
        d.arrow(mty, over_pr)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.clear_below,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(SWEEP_WRAP_HEIGHT),
    })
}

/// Admit `Rat.echelonAux : Nat -> Nat -> Nat -> Mat -> Nat -> Nat -> Mat`,
/// `echelonAux rows cols fuel M pr pc` — one Gaussian-elimination step per unit
/// of fuel.
///
/// The step is: stop if the pivot row or the pivot column has run past the
/// bound; otherwise find a pivot in column `pc` at or below row `pr`. If there
/// is none the column is already clear and only `pc` advances. If there is one,
/// swap it into place, clear everything below it, and advance both cursors.
///
/// `pc` advances on BOTH branches, which is what makes fuel `cols` exact in
/// [`declare_row_echelon`].
fn declare_echelon_aux(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let mty = mat_ty(d);

    let rows_fv = d.fresh_fvar();
    let rows = d.kernel().fvar(rows_fv);
    let cols_fv = d.fresh_fvar();
    let cols = d.kernel().fvar(cols_fv);

    let inner_ty = {
        let over_pc = d.arrow(nat, mty);
        let over_pr = d.arrow(nat, over_pc);
        d.arrow(mty, over_pr)
    };

    let zero_case = {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let pr_fv = d.fresh_fvar();
        let pc_fv = d.fresh_fvar();
        let over_pc = d.lam_fv(pc_fv, nat, m);
        let over_pr = d.lam_fv(pr_fv, nat, over_pc);
        d.lam_fv(m_fv, mty, over_pr)
    };
    let succ_case = {
        let n_fv = d.fresh_fvar();
        let ih_fv = d.fresh_fvar();
        let ih = d.kernel().fvar(ih_fv);
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let pr_fv = d.fresh_fvar();
        let pr = d.kernel().fvar(pr_fv);
        let pc_fv = d.fresh_fvar();
        let pc = d.kernel().fvar(pc_fv);

        let spr = d.succ(pr);
        let spc = d.succ(pc);

        let piv = rpivot_search(d, p, m, pc, pr, rows);
        let swapped = rrow_swap(d, p, pr, piv, m);
        let cleared = rclear_below(d, p, swapped, pr, pc, rows);
        let advance_both = d.apply(ih, &[cleared, spr, spc]);
        let advance_column = d.apply(ih, &[m, pr, spc]);
        let no_pivot = NatOps::ble(d, rows, piv);
        let step = bool_select_at(d, mty, no_pivot, advance_column, advance_both);

        let cols_done = NatOps::ble(d, cols, pc);
        let after_cols = bool_select_at(d, mty, cols_done, m, step);
        let rows_done = NatOps::ble(d, rows, pr);
        let body = bool_select_at(d, mty, rows_done, m, after_cols);

        let over_pc = d.lam_fv(pc_fv, nat, body);
        let over_pr = d.lam_fv(pr_fv, nat, over_pc);
        let over_m = d.lam_fv(m_fv, mty, over_pr);
        let over_ih = d.lam_fv(ih_fv, inner_ty, over_m);
        d.lam_fv(n_fv, nat, over_ih)
    };

    let fuel_fv = d.fresh_fvar();
    let fuel = d.kernel().fvar(fuel_fv);
    let rec_app = nat_fuel_rec(d, inner_ty, zero_case, succ_case, fuel);
    let m_outer_fv = d.fresh_fvar();
    let m_outer = d.kernel().fvar(m_outer_fv);
    let pr_outer_fv = d.fresh_fvar();
    let pr_outer = d.kernel().fvar(pr_outer_fv);
    let pc_outer_fv = d.fresh_fvar();
    let pc_outer = d.kernel().fvar(pc_outer_fv);
    let applied = d.apply(rec_app, &[m_outer, pr_outer, pc_outer]);

    let value = {
        let over_pc = d.lam_fv(pc_outer_fv, nat, applied);
        let over_pr = d.lam_fv(pr_outer_fv, nat, over_pc);
        let over_m = d.lam_fv(m_outer_fv, mty, over_pr);
        let over_fuel = d.lam_fv(fuel_fv, nat, over_m);
        let over_cols = d.lam_fv(cols_fv, nat, over_fuel);
        d.lam_fv(rows_fv, nat, over_cols)
    };
    let ty = {
        let over_pc = d.arrow(nat, mty);
        let over_pr = d.arrow(nat, over_pc);
        let over_m = d.arrow(mty, over_pr);
        let over_fuel = d.arrow(nat, over_m);
        let over_cols = d.arrow(nat, over_fuel);
        d.arrow(nat, over_cols)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.echelon_aux,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(DRIVER_HEIGHT),
    })
}

/// Admit `Rat.rowEchelon : Mat -> Nat -> Nat -> Mat`,
/// `rowEchelon M rows cols := echelonAux rows cols cols M 0 0`.
fn declare_row_echelon(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let mty = mat_ty(d);

    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let rows_fv = d.fresh_fvar();
    let rows = d.kernel().fvar(rows_fv);
    let cols_fv = d.fresh_fvar();
    let cols = d.kernel().fvar(cols_fv);

    let zero_n = d.zero();
    let body = d.const_app(p.echelon_aux, &[rows, cols, cols, m, zero_n, zero_n]);
    let value = {
        let over_cols = d.lam_fv(cols_fv, nat, body);
        let over_rows = d.lam_fv(rows_fv, nat, over_cols);
        d.lam_fv(m_fv, mty, over_rows)
    };
    let ty = {
        let over_cols = d.arrow(nat, mty);
        let over_rows = d.arrow(nat, over_cols);
        d.arrow(mty, over_rows)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.row_echelon,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(ENTRY_HEIGHT),
    })
}

/// Admit `Rat.leadingIndexAux : Mat -> Nat -> Nat -> Nat -> Nat -> Nat`,
/// `leadingIndexAux M r cols fuel c`.
fn declare_leading_index_aux(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let mty = mat_ty(d);

    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let r_fv = d.fresh_fvar();
    let r = d.kernel().fvar(r_fv);
    let cols_fv = d.fresh_fvar();
    let cols = d.kernel().fvar(cols_fv);

    let inner_ty = d.arrow(nat, nat);

    let zero_case = {
        let c_fv = d.fresh_fvar();
        d.lam_fv(c_fv, nat, cols)
    };
    let succ_case = {
        let n_fv = d.fresh_fvar();
        let ih_fv = d.fresh_fvar();
        let ih = d.kernel().fvar(ih_fv);
        let c_fv = d.fresh_fvar();
        let c = d.kernel().fvar(c_fv);

        let entry = d.apply(m, &[r, c]);
        let is_zero = ris_zero_b(d, p, entry);
        let sc = d.succ(c);
        let recurse = d.apply(ih, &[sc]);
        let keep_looking = bool_select_at(d, nat, is_zero, recurse, c);
        let out_of_range = NatOps::ble(d, cols, c);
        let body = bool_select_at(d, nat, out_of_range, cols, keep_looking);

        let over_c = d.lam_fv(c_fv, nat, body);
        let over_ih = d.lam_fv(ih_fv, inner_ty, over_c);
        d.lam_fv(n_fv, nat, over_ih)
    };

    let fuel_fv = d.fresh_fvar();
    let fuel = d.kernel().fvar(fuel_fv);
    let rec_app = nat_fuel_rec(d, inner_ty, zero_case, succ_case, fuel);
    let c_outer_fv = d.fresh_fvar();
    let c_outer = d.kernel().fvar(c_outer_fv);
    let applied = d.apply(rec_app, &[c_outer]);

    let value = {
        let over_c = d.lam_fv(c_outer_fv, nat, applied);
        let over_fuel = d.lam_fv(fuel_fv, nat, over_c);
        let over_cols = d.lam_fv(cols_fv, nat, over_fuel);
        let over_r = d.lam_fv(r_fv, nat, over_cols);
        d.lam_fv(m_fv, mty, over_r)
    };
    let ty = {
        let over_c = d.arrow(nat, nat);
        let over_fuel = d.arrow(nat, over_c);
        let over_cols = d.arrow(nat, over_fuel);
        let over_r = d.arrow(nat, over_cols);
        d.arrow(mty, over_r)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.leading_index_aux,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(SEARCH_AUX_HEIGHT),
    })
}

/// Admit `Rat.leadingIndex : Mat -> Nat -> Nat -> Nat`,
/// `leadingIndex M r cols := leadingIndexAux M r cols cols 0`.
///
/// `cols` for a zero row is deliberate and load-bearing: it makes the
/// "strictly increasing, zero rows last" test one comparison
/// ([`declare_echelon_step_ok`]) rather than a three-way case analysis, and it
/// is the value `rank` will count against.
fn declare_leading_index(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let mty = mat_ty(d);

    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let r_fv = d.fresh_fvar();
    let r = d.kernel().fvar(r_fv);
    let cols_fv = d.fresh_fvar();
    let cols = d.kernel().fvar(cols_fv);

    let zero_n = d.zero();
    let body = d.const_app(p.leading_index_aux, &[m, r, cols, cols, zero_n]);
    let value = {
        let over_cols = d.lam_fv(cols_fv, nat, body);
        let over_r = d.lam_fv(r_fv, nat, over_cols);
        d.lam_fv(m_fv, mty, over_r)
    };
    let ty = {
        let over_cols = d.arrow(nat, nat);
        let over_r = d.arrow(nat, over_cols);
        d.arrow(mty, over_r)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.leading_index,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(SWEEP_HEIGHT),
    })
}

/// Admit `Rat.echelonStepOk : Nat -> Nat -> Nat -> Bool`,
/// `echelonStepOk l1 l2 cols := ble (succ l1) l2 || (ble cols l1 && ble cols l2)`.
///
/// A leading index is always at most `cols`, so `ble cols l` says exactly
/// `l = cols`, i.e. "that row is zero". The disjunction is therefore "the
/// leading entry moved strictly right" OR "both rows are zero" — and the second
/// clause needs BOTH conjuncts: dropping `ble cols l2` would accept a nonzero
/// row sitting below a zero one, which is precisely what echelon form forbids.
fn declare_echelon_step_ok(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let bool_ty = d.bool_ty();

    let l1_fv = d.fresh_fvar();
    let l1 = d.kernel().fvar(l1_fv);
    let l2_fv = d.fresh_fvar();
    let l2 = d.kernel().fvar(l2_fv);
    let cols_fv = d.fresh_fvar();
    let cols = d.kernel().fvar(cols_fv);

    let sl1 = d.succ(l1);
    let strict = NatOps::ble(d, sl1, l2);
    let first_zero = NatOps::ble(d, cols, l1);
    let second_zero = NatOps::ble(d, cols, l2);
    let false_v = d.bool_false();
    let both_zero = bool_select_at(d, bool_ty, first_zero, second_zero, false_v);
    let true_v = d.bool_true();
    let body = bool_select_at(d, bool_ty, strict, true_v, both_zero);

    let value = {
        let over_cols = d.lam_fv(cols_fv, nat, body);
        let over_l2 = d.lam_fv(l2_fv, nat, over_cols);
        d.lam_fv(l1_fv, nat, over_l2)
    };
    let ty = {
        let over_cols = d.arrow(nat, bool_ty);
        let over_l2 = d.arrow(nat, over_cols);
        d.arrow(nat, over_l2)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.echelon_step_ok,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(LEAF_HEIGHT),
    })
}

/// Admit `Rat.isEchelonAux : Mat -> Nat -> Nat -> Nat -> Nat -> Bool`,
/// `isEchelonAux M rows cols fuel r` — every adjacent pair from `r` upward
/// passes [`declare_echelon_step_ok`].
fn declare_is_echelon_aux(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let mty = mat_ty(d);
    let bool_ty = d.bool_ty();

    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let rows_fv = d.fresh_fvar();
    let rows = d.kernel().fvar(rows_fv);
    let cols_fv = d.fresh_fvar();
    let cols = d.kernel().fvar(cols_fv);

    let inner_ty = d.arrow(nat, bool_ty);

    let zero_case = {
        let r_fv = d.fresh_fvar();
        let true_v = d.bool_true();
        d.lam_fv(r_fv, nat, true_v)
    };
    let succ_case = {
        let n_fv = d.fresh_fvar();
        let ih_fv = d.fresh_fvar();
        let ih = d.kernel().fvar(ih_fv);
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);

        let sr = d.succ(r);
        let l1 = rleading_index(d, p, m, r, cols);
        let l2 = rleading_index(d, p, m, sr, cols);
        let ok = d.const_app(p.echelon_step_ok, &[l1, l2, cols]);
        let recurse = d.apply(ih, &[sr]);
        let false_v = d.bool_false();
        let step = bool_select_at(d, bool_ty, ok, recurse, false_v);
        let last_row = NatOps::ble(d, rows, sr);
        let true_v = d.bool_true();
        let body = bool_select_at(d, bool_ty, last_row, true_v, step);

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
        let over_cols = d.lam_fv(cols_fv, nat, over_fuel);
        let over_rows = d.lam_fv(rows_fv, nat, over_cols);
        d.lam_fv(m_fv, mty, over_rows)
    };
    let ty = {
        let over_r = d.arrow(nat, bool_ty);
        let over_fuel = d.arrow(nat, over_r);
        let over_cols = d.arrow(nat, over_fuel);
        let over_rows = d.arrow(nat, over_cols);
        d.arrow(mty, over_rows)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.is_echelon_aux,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(SWEEP_WRAP_HEIGHT),
    })
}

/// Admit `Rat.isEchelon : Mat -> Nat -> Nat -> Bool`,
/// `isEchelon M rows cols := isEchelonAux M rows cols rows 0`.
fn declare_is_echelon(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let mty = mat_ty(d);
    let bool_ty = d.bool_ty();

    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let rows_fv = d.fresh_fvar();
    let rows = d.kernel().fvar(rows_fv);
    let cols_fv = d.fresh_fvar();
    let cols = d.kernel().fvar(cols_fv);

    let zero_n = d.zero();
    let body = d.const_app(p.is_echelon_aux, &[m, rows, cols, rows, zero_n]);
    let value = {
        let over_cols = d.lam_fv(cols_fv, nat, body);
        let over_rows = d.lam_fv(rows_fv, nat, over_cols);
        d.lam_fv(m_fv, mty, over_rows)
    };
    let ty = {
        let over_cols = d.arrow(nat, bool_ty);
        let over_rows = d.arrow(nat, over_cols);
        d.arrow(mty, over_rows)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.is_echelon,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(DRIVER_HEIGHT),
    })
}

// --- the decided zero test agrees with the propositional one ---------------

/// `heq : Eq Bool cond true ⊢ Eq Bool (bool_select_at Bool cond a b) a` — the
/// `Bool`-valued twin of `select_rat_true`.
fn select_bool_true(d: &mut IntDev<'_>, cond: ExprId, a: ExprId, b: ExprId, heq: ExprId) -> ExprId {
    let true_val = d.bool_true();
    let symm_hb = d.bool_symm(cond, true_val, heq);
    let motive = d.bool_eq_motive(true_val, &|d, value| {
        let bool_ty = d.bool_ty();
        let sel = bool_select_at(d, bool_ty, value, a, b);
        d.bool_eq(sel, a)
    });
    let refl_case = d.bool_refl(a);
    d.bool_transport(true_val, motive, refl_case, cond, symm_hb)
}

/// `heq : Eq Bool cond false ⊢ Eq Bool (bool_select_at Bool cond a b) b`.
fn select_bool_false(
    d: &mut IntDev<'_>,
    cond: ExprId,
    a: ExprId,
    b: ExprId,
    heq: ExprId,
) -> ExprId {
    let false_val = d.bool_false();
    let symm_hb = d.bool_symm(cond, false_val, heq);
    let motive = d.bool_eq_motive(false_val, &|d, value| {
        let bool_ty = d.bool_ty();
        let sel = bool_select_at(d, bool_ty, value, a, b);
        d.bool_eq(sel, b)
    });
    let refl_case = d.bool_refl(b);
    d.bool_transport(false_val, motive, refl_case, cond, symm_hb)
}

/// Admit `Rat.isZeroB_zero : Rat.isZeroB Rat.zero = Bool.true`.
///
/// `Eq.refl`. `Rat.zero` is built with `Rat.mk` so both projections compute,
/// and `Rat.ble` decides by cross-multiplication into `Int.ble`, so both
/// comparisons ι-reduce and the nested `Bool.rec` fires.
fn declare_is_zero_b_zero(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let zero = rzero(d, p);
    let lhs = ris_zero_b(d, p, zero);
    let true_v = d.bool_true();
    let ty = d.bool_eq(lhs, true_v);
    let value = d.bool_refl(true_v);
    d.declare_theorem(p.is_zero_b_zero, ty, value)
}

/// Admit `Rat.eq_zero_of_isZeroB : ∀ x, Rat.isZeroB x = Bool.true →
/// Eq Rat x Rat.zero`.
///
/// **This is the bridge `rank` needs, and it is the only place the decided test
/// has to be reconciled with the propositional one.** Split on `Rat.ble x 0`:
/// its `true` branch reduces `isZeroB x` to `Rat.ble 0 x`, so the hypothesis
/// becomes the second comparison and `Rat.le_antisymm` closes it from the two
/// `Rat.le_of_ble_eq_true` bridges. Its `false` branch reduces `isZeroB x` to
/// `Bool.false`, contradicting the hypothesis.
fn declare_eq_zero_of_is_zero_b(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let carrier = rat_ty(d);

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let zero = rzero(d, p);
    let test = ris_zero_b(d, p, x);
    let true_v = d.bool_true();
    let false_v = d.bool_false();
    let h_ty = d.bool_eq(test, true_v);
    let target = req(d, x, zero);

    let upper = rble(d, p, x, zero);
    let lower = rble(d, p, zero, x);

    let at_true = {
        let g_fv = d.fresh_fvar();
        let g = d.kernel().fvar(g_fv);
        let g_ty = d.bool_eq(upper, true_v);
        // `isZeroB x = ble 0 x`, so the hypothesis carries over to it.
        let sel = select_bool_true(d, upper, lower, false_v, g);
        let flipped = d.bool_symm(test, lower, sel);
        let lower_true = d.bool_trans(lower, test, true_v, flipped, h);
        let le_upper = d.lemma(p.le_of_ble_eq_true, &[x, zero, g]);
        let le_lower = d.lemma(p.le_of_ble_eq_true, &[zero, x, lower_true]);
        let body = d.lemma(p.le_antisymm, &[x, zero, le_upper, le_lower]);
        d.lam_fv(g_fv, g_ty, body)
    };
    let at_false = {
        let g_fv = d.fresh_fvar();
        let g = d.kernel().fvar(g_fv);
        let g_ty = d.bool_eq(upper, false_v);
        let sel = select_bool_false(d, upper, lower, false_v, g);
        let flipped = d.bool_symm(test, false_v, sel);
        let bad = d.bool_trans(false_v, test, true_v, flipped, h);
        let body = d.false_true_elim(target, bad);
        d.lam_fv(g_fv, g_ty, body)
    };
    let proof = bool_cases_eq(d, upper, target, at_true, at_false);

    let ty = {
        let over_h = d.pi_fv(h_fv, h_ty, target);
        d.pi_fv(x_fv, carrier, over_h)
    };
    let value = {
        let over_h = d.lam_fv(h_fv, h_ty, proof);
        d.lam_fv(x_fv, carrier, over_h)
    };
    d.declare_theorem(p.eq_zero_of_is_zero_b, ty, value)
}

/// Admit `Rat.isZeroB_of_eq_zero : ∀ x, Eq Rat x Rat.zero →
/// Rat.isZeroB x = Bool.true` — the converse, by transporting
/// [`declare_is_zero_b_zero`] along the equation.
fn declare_is_zero_b_of_eq_zero(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let carrier = rat_ty(d);

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let zero = rzero(d, p);
    let h_ty = req(d, x, zero);
    let test = ris_zero_b(d, p, x);
    let true_v = d.bool_true();
    let concl = d.bool_eq(test, true_v);

    let base = d.lemma(p.is_zero_b_zero, &[]);
    let flipped = rsymm(d, x, zero, h);
    let proof = rat_eq_rewrite(d, zero, x, flipped, base, &|d, y| {
        let t = ris_zero_b(d, p, y);
        let true_v = d.bool_true();
        d.bool_eq(t, true_v)
    });

    let ty = {
        let over_h = d.pi_fv(h_fv, h_ty, concl);
        d.pi_fv(x_fv, carrier, over_h)
    };
    let value = {
        let over_h = d.lam_fv(h_fv, h_ty, proof);
        d.lam_fv(x_fv, carrier, over_h)
    };
    d.declare_theorem(p.is_zero_b_of_eq_zero, ty, value)
}

/// Admit `Rat.ne_zero_of_isZeroB_false : ∀ x, Rat.isZeroB x = Bool.false →
/// Not (Eq Rat x Rat.zero)`.
///
/// The form the pivot's nonzero-ness arrives in: `Rat.pivotSearch` returns an
/// index because `isZeroB` said `false` there, and every field law that could
/// then divide by it — `Rat.mul_inv_cancel_of_ne_zero` above all — wants
/// `Not (Eq x 0)`.
fn declare_ne_zero_of_is_zero_b_false(
    d: &mut IntDev<'_>,
    p: RatPrelude,
) -> Result<(), KernelError> {
    let carrier = rat_ty(d);

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);
    let e_fv = d.fresh_fvar();
    let e = d.kernel().fvar(e_fv);

    let zero = rzero(d, p);
    let test = ris_zero_b(d, p, x);
    let false_v = d.bool_false();
    let true_v = d.bool_true();
    let h_ty = d.bool_eq(test, false_v);
    let e_ty = req(d, x, zero);
    let logic = d.prelude().logic;
    let false_prop = d.kernel().const_(logic.false_, vec![]);

    // Move the hypothesis to `x := 0`, where `isZeroB` is known to be `true`.
    let at_zero = rat_eq_rewrite(d, x, zero, e, h, &|d, y| {
        let t = ris_zero_b(d, p, y);
        let false_v = d.bool_false();
        d.bool_eq(t, false_v)
    });
    let zero_test = ris_zero_b(d, p, zero);
    let base = d.lemma(p.is_zero_b_zero, &[]);
    let flipped = d.bool_symm(zero_test, false_v, at_zero);
    let bad = d.bool_trans(false_v, zero_test, true_v, flipped, base);
    let body = d.false_true_elim(false_prop, bad);

    let ty = {
        let over_e = d.pi_fv(e_fv, e_ty, false_prop);
        let over_h = d.pi_fv(h_fv, h_ty, over_e);
        d.pi_fv(x_fv, carrier, over_h)
    };
    let value = {
        let over_e = d.lam_fv(e_fv, e_ty, body);
        let over_h = d.lam_fv(h_fv, h_ty, over_e);
        d.lam_fv(x_fv, carrier, over_h)
    };
    d.declare_theorem(p.ne_zero_of_is_zero_b_false, ty, value)
}
