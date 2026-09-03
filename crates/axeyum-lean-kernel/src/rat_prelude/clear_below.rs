//! `Rat.clearBelow`'s postcondition — ADR-1554's **obligation 3**.
//!
//! ## The statement, in two halves
//!
//! ADR-1554 sizes obligation 3 as
//!
//! > For every `r` in `(pr, rows)` the swept matrix has `0` at `(r, pc)`, and
//! > rows outside that range are untouched. The arithmetic core is
//! > `a + (-(a/b)) * b = 0` given `b ≠ 0`.
//!
//! Both halves land here, and the OFF half is not a convenience: it is what the
//! ZERO half's own proof consumes. When the sweep reaches the target row it
//! rewrites it once and then keeps recursing on rows STRICTLY BELOW, so the
//! value the caller asked about is fixed by the rows the loop has not visited
//! yet. That is exactly [`RatPrelude::clear_below_aux_off`], instantiated at the
//! row just cleared. Proving the zero half without it would mean re-deriving it
//! inline.
//!
//! ```text
//! Rat.clearBelowAux_off  : ∀ pr pc rows q c fuel M r, Lt q r →
//!                            clearBelowAux pr pc rows fuel M r q c = M q c
//! Rat.clearBelow_off     : ∀ M pr pc rows q c, Le q pr →
//!                            clearBelow M pr pc rows q c = M q c
//! Rat.clearBelowAux_zero : ∀ pr pc rows q fuel M r, Lt pr r → Le r q →
//!                            Lt q rows → Lt q (r + fuel) → M pr pc ≠ 0 →
//!                            clearBelowAux pr pc rows fuel M r q pc = 0
//! Rat.clearBelow_zero    : ∀ M pr pc rows q, Lt pr q → Lt q rows → M pr pc ≠ 0 →
//!                            clearBelow M pr pc rows q pc = 0
//! ```
//!
//! ## Why the fuel bound is a hypothesis and not a derived fact
//!
//! `clearBelowAux` answers `M` when its fuel runs out, exactly as it does when
//! the row cursor passes `rows`. Those two exhaustion routes are
//! indistinguishable in the answer, so the zero half cannot be true of an
//! arbitrary fuel: with `fuel = 0` the sweep returns `M` untouched and `M q pc`
//! is whatever it was. The hypothesis `Lt q (r + fuel)` — *the target row is
//! within the `fuel` rows this call will visit* — is the weakest thing that
//! rules that out, and the wrapper discharges it from `Lt q rows` because
//! `clearBelow` hands the loop `rows` units of fuel.
//!
//! The OFF half needs no such hypothesis: a row ABOVE the cursor is untouched
//! whether the loop finishes or gives up, so its statement is unconditional in
//! the fuel. That asymmetry is why the two halves are separate inductions
//! rather than a conjunction carried through one.
//!
//! ## What each induction generalises
//!
//! Both recurse on the fuel with **`M` and `r` inside the motive**, because the
//! step feeds the recursion a rewritten matrix at the next row. `pr`, `pc`,
//! `rows`, the target row `q` and the column sit outside — they are the same at
//! every level.
//!
//! The nonzero-pivot hypothesis has to travel with the matrix, so it too is
//! inside the motive, and re-establishing it at each step is one application of
//! `Rat.rowAddMul_off`: the sweep rewrites row `r`, and `pr < r`, so the pivot
//! entry is not the entry that changed. **That side condition is the whole
//! reason `Lt pr r` is a hypothesis** rather than the weaker `Le pr r` the
//! statement would otherwise want — at `pr = r` the sweep would clear the pivot
//! row against itself and the hypothesis would be destroyed by the first step.
//!
//! ## The splits, and which are free
//!
//! ADR-1562 §3 records the rule: *a split is free exactly when neither branch's
//! proof mentions the tested `Bool`.* Here the `Nat.ble rows r` split is NOT
//! free in either induction — in the OFF half its `true` branch is where the
//! answer is literally `M`, and in the ZERO half the same branch has to be
//! REFUTED from `Le r q` and `Lt q rows`. The second split in the zero half, on
//! `Nat.lt_or_eq_of_le r q`, is not a `Bool` split at all: it is where the
//! target row is either the one this step clears (`r = q`, the arithmetic
//! fires) or still below (`r < q`, the induction hypothesis fires), and those
//! are the only two shapes the postcondition has.

use super::RatPrelude;
use super::echelon::{bool_select_at, rdiv, rinv, rrow_add_mul};
use super::matrix_det::mat_ty;
use super::ops::{
    nat_rewrite_prop, radd, rat_ty, rchain, rcongr, req, rmul, rneg, rone, rrefl, rsymm, rtrans,
    rzero,
};
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
pub(super) fn declare_clear_below_post(
    d: &mut IntDev<'_>,
    p: RatPrelude,
) -> Result<(), KernelError> {
    declare_add_neg_div_mul_cancel(d, p)?;
    declare_clear_below_aux_off(d, p)?;
    declare_clear_below_off(d, p)?;
    declare_clear_below_aux_zero(d, p)?;
    declare_clear_below_zero(d, p)?;
    declare_clear_below_aux_preserves_zero(d, p)?;
    declare_clear_below_preserves_zero(d, p)?;
    Ok(())
}

/// `Not (Eq Rat x Rat.zero)`.
fn ne_zero(d: &mut IntDev<'_>, p: RatPrelude, x: ExprId) -> ExprId {
    let zero_r = rzero(d, p);
    let equation = req(d, x, zero_r);
    d.not(equation)
}

/// Admit `Rat.add_neg_div_mul_cancel : ∀ a b, Not (Eq Rat b Rat.zero) →
/// Eq Rat (Rat.add a (Rat.mul (Rat.neg (Rat.div a b)) b)) Rat.zero`.
///
/// The arithmetic core ADR-1554 names for obligation 3, stated at the exact
/// shape `Rat.clearBelowAux` produces: the row operation multiplies by
/// `-(a/b)` on the LEFT, and `Rat.mul_neg` is stated with the negation on the
/// right, so the first two steps are the two `Rat.mul_comm` applications that
/// move it across. `Rat.div` is a `Definition` that unfolds to `a * inv b`, so
/// `Rat.mul_assoc` applies to the quotient without a rewrite.
fn declare_add_neg_div_mul_cancel(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let carrier = rat_ty(d);

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let hyp_ty = ne_zero(d, p, b);
    let quotient = rdiv(d, p, a, b);
    let factor = rneg(d, quotient);
    let scaled = rmul(d, factor, b);
    let lhs = radd(d, a, scaled);
    let zero_r = rzero(d, p);
    let stmt = req(d, lhs, zero_r);

    // (1) `(a / b) * b = a`, spending the nonzero hypothesis exactly once.
    let inv_b = rinv(d, p, b);
    let quotient_times_b = rmul(d, quotient, b);
    let inner = rmul(d, inv_b, b);
    let assoc = d.lemma(p.mul_assoc, &[a, inv_b, b]);
    let inv_mul_one = {
        let flipped = rmul(d, b, inv_b);
        let comm = d.lemma(p.mul_comm, &[inv_b, b]);
        let cancel = d.lemma(p.mul_inv_cancel_of_ne_zero, &[b, h]);
        let one_r = rone(d, p);
        rtrans(d, inner, flipped, one_r, comm, cancel)
    };
    let one_r = rone(d, p);
    let lifted = rcongr(d, inner, one_r, inv_mul_one, &|d, t| rmul(d, a, t));
    let mul_one = d.lemma(p.mul_one, &[a]);
    let a_times_inner = rmul(d, a, inner);
    let a_times_one = rmul(d, a, one_r);
    let (_, quotient_b_eq_a) = rchain(
        d,
        quotient_times_b,
        &[(a_times_inner, assoc), (a_times_one, lifted), (a, mul_one)],
    );

    // (2) `(-(a/b)) * b = -a`, moving the negation across two `mul_comm`s.
    let b_times_factor = rmul(d, b, factor);
    let b_quotient = rmul(d, b, quotient);
    let neg_b_quotient = rneg(d, b_quotient);
    let neg_quotient_b = rneg(d, quotient_times_b);
    let neg_a = rneg(d, a);
    let comm_out = d.lemma(p.mul_comm, &[factor, b]);
    let across = d.lemma(p.mul_neg, &[b, quotient]);
    let comm_in = d.lemma(p.mul_comm, &[b, quotient]);
    let under_neg = rcongr(d, b_quotient, quotient_times_b, comm_in, &|d, t| rneg(d, t));
    let to_neg_a = rcongr(d, quotient_times_b, a, quotient_b_eq_a, &|d, t| rneg(d, t));
    let (_, scaled_eq_neg_a) = rchain(
        d,
        scaled,
        &[
            (b_times_factor, comm_out),
            (neg_b_quotient, across),
            (neg_quotient_b, under_neg),
            (neg_a, to_neg_a),
        ],
    );

    // (3) `a + (-a) = 0`.
    let a_plus_neg_a = radd(d, a, neg_a);
    let in_sum = rcongr(d, scaled, neg_a, scaled_eq_neg_a, &|d, t| radd(d, a, t));
    let add_neg = d.lemma(p.add_neg, &[a]);
    let (_, proof) = rchain(d, lhs, &[(a_plus_neg_a, in_sum), (zero_r, add_neg)]);

    let ty = {
        let over_h = d.pi_fv(h_fv, hyp_ty, stmt);
        let over_b = d.pi_fv(b_fv, carrier, over_h);
        d.pi_fv(a_fv, carrier, over_b)
    };
    let value = {
        let over_h = d.lam_fv(h_fv, hyp_ty, proof);
        let over_b = d.lam_fv(b_fv, carrier, over_h);
        d.lam_fv(a_fv, carrier, over_b)
    };
    d.declare_theorem(p.add_neg_div_mul_cancel, ty, value)
}

/// `Not (Eq Nat x y)` from `h : Lt x y` — `x = y` would make `h : Lt y y`.
fn ne_of_lt_nat(d: &mut IntDev<'_>, x: ExprId, y: ExprId, h: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let equation = d.eq(x, y);
    let he_fv = d.fresh_fvar();
    let he = d.kernel().fvar(he_fv);
    let moved = nat_rewrite_prop(d, x, y, he, h, &|d, t| NatOps::lt(d, t, y));
    let lt_irrefl = d.prelude().lt_irrefl;
    let contradiction = d.lemma(lt_irrefl, &[y, moved]);
    let _ = nat;
    d.lam_fv(he_fv, equation, contradiction)
}

/// `Eq Bool (Nat.beq x y) Bool.false` from `h : Lt x y`.
fn beq_false_of_lt(d: &mut IntDev<'_>, x: ExprId, y: ExprId, h: ExprId) -> ExprId {
    let ne = ne_of_lt_nat(d, x, y, h);
    let beq_eq_false_of_ne = d.prelude().beq_eq_false_of_ne;
    d.lemma(beq_eq_false_of_ne, &[x, y, ne])
}

/// Admit `Rat.clearBelowAux_off : ∀ pr pc rows q c fuel M r, Lt q r →
/// Eq Rat (clearBelowAux pr pc rows fuel M r q c) (M q c)`.
///
/// *A row strictly above the sweep's cursor is untouched, whatever the fuel.*
/// Fuel induction with `M` and `r` in the motive; the step's `false` branch
/// applies the induction hypothesis at the rewritten matrix and the next row,
/// then strips the rewrite with `Rat.rowAddMul_off` — whose `Nat.beq q r =
/// false` side condition is exactly the hypothesis, since `Lt q r`.
fn declare_clear_below_aux_off(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let mty = mat_ty(d);

    let pr_fv = d.fresh_fvar();
    let pr = d.kernel().fvar(pr_fv);
    let pc_fv = d.fresh_fvar();
    let pc = d.kernel().fvar(pc_fv);
    let rows_fv = d.fresh_fvar();
    let rows = d.kernel().fvar(rows_fv);
    let q_fv = d.fresh_fvar();
    let q = d.kernel().fvar(q_fv);
    let col_fv = d.fresh_fvar();
    let col = d.kernel().fvar(col_fv);
    let fuel_fv = d.fresh_fvar();
    let fuel = d.kernel().fvar(fuel_fv);

    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        let swept = d.const_app(p.clear_below_aux, &[pr, pc, rows, x, m, r]);
        let lhs = d.apply(swept, &[q, col]);
        let rhs = d.apply(m, &[q, col]);
        let concl = req(d, lhs, rhs);
        let hyp = NatOps::lt(d, q, r);
        let body = d.arrow(hyp, concl);
        let over_r = d.pi_fv(r_fv, nat, body);
        d.pi_fv(m_fv, mty, over_r)
    };
    let stmt = motive(d, fuel);

    let base = |d: &mut IntDev<'_>| -> ExprId {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        let hyp = NatOps::lt(d, q, r);
        let h_fv = d.fresh_fvar();
        let entry = d.apply(m, &[q, col]);
        let refl = rrefl(d, entry);
        let with_h = d.lam_fv(h_fv, hyp, refl);
        let over_r = d.lam_fv(r_fv, nat, with_h);
        d.lam_fv(m_fv, mty, over_r)
    };

    let step = |d: &mut IntDev<'_>, n: ExprId, ih: ExprId| -> ExprId {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let hyp = NatOps::lt(d, q, r);

        let here = d.apply(m, &[r, pc]);
        let pivot = d.apply(m, &[pr, pc]);
        let ratio = rdiv(d, p, here, pivot);
        let factor = rneg(d, ratio);
        let updated = rrow_add_mul(d, p, r, pr, factor, m);
        let sr = d.succ(r);
        let recursed = d.const_app(p.clear_below_aux, &[pr, pc, rows, n, updated, sr]);
        let oor = NatOps::ble(d, rows, r);

        let shape = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
            let sel = bool_select_at(d, mty, x, m, recursed);
            let lhs = d.apply(sel, &[q, col]);
            let rhs = d.apply(m, &[q, col]);
            req(d, lhs, rhs)
        };
        let goal = shape(d, oor);

        let true_ = d.bool_true();
        let false_ = d.bool_false();
        let h_true_ty = d.bool_eq(oor, true_);
        let h_false_ty = d.bool_eq(oor, false_);

        let left_minor = {
            let ht_fv = d.fresh_fvar();
            let ht = d.kernel().fvar(ht_fv);
            let motive_x = d.bool_eq_motive(true_, &shape);
            let entry = d.apply(m, &[q, col]);
            let refl_case = rrefl(d, entry);
            let ht_sym = d.bool_symm(oor, true_, ht);
            let body = d.bool_transport(true_, motive_x, refl_case, oor, ht_sym);
            d.lam_fv(ht_fv, h_true_ty, body)
        };

        let right_minor = {
            let hf_fv = d.fresh_fvar();
            let hf = d.kernel().fvar(hf_fv);

            let le_trans = d.prelude().le_trans;
            let le_succ = d.prelude().le_succ;
            let sq = d.succ(q);
            let step_up = d.lemma(le_succ, &[r]);
            let lt_q_sr = d.lemma(le_trans, &[sq, r, sr, h, step_up]);
            let ih_app = d.apply(ih, &[updated, sr, lt_q_sr]);

            let hbeq = beq_false_of_lt(d, q, r, h);
            let off = d.lemma(p.row_add_mul_off, &[r, pr, factor, m, q, hbeq, col]);

            let at_recursed = d.apply(recursed, &[q, col]);
            let at_updated = d.apply(updated, &[q, col]);
            let at_m = d.apply(m, &[q, col]);
            let refl_case = rtrans(d, at_recursed, at_updated, at_m, ih_app, off);

            let motive_x = d.bool_eq_motive(false_, &shape);
            let hf_sym = d.bool_symm(oor, false_, hf);
            let body = d.bool_transport(false_, motive_x, refl_case, oor, hf_sym);
            d.lam_fv(hf_fv, h_false_ty, body)
        };

        let split = bool_cases(d, oor);
        let chosen = or_cases(
            d,
            h_true_ty,
            h_false_ty,
            goal,
            left_minor,
            right_minor,
            split,
        );
        let with_h = d.lam_fv(h_fv, hyp, chosen);
        let over_r = d.lam_fv(r_fv, nat, with_h);
        d.lam_fv(m_fv, mty, over_r)
    };

    let proof = d.induct(&motive, &base, &step, fuel);

    let ty = {
        let over_fuel = d.pi_fv(fuel_fv, nat, stmt);
        let over_col = d.pi_fv(col_fv, nat, over_fuel);
        let over_q = d.pi_fv(q_fv, nat, over_col);
        let over_rows = d.pi_fv(rows_fv, nat, over_q);
        let over_pc = d.pi_fv(pc_fv, nat, over_rows);
        d.pi_fv(pr_fv, nat, over_pc)
    };
    let value = {
        let over_fuel = d.lam_fv(fuel_fv, nat, proof);
        let over_col = d.lam_fv(col_fv, nat, over_fuel);
        let over_q = d.lam_fv(q_fv, nat, over_col);
        let over_rows = d.lam_fv(rows_fv, nat, over_q);
        let over_pc = d.lam_fv(pc_fv, nat, over_rows);
        d.lam_fv(pr_fv, nat, over_pc)
    };
    d.declare_theorem(p.clear_below_aux_off, ty, value)
}

/// Admit `Rat.clearBelow_off : ∀ M pr pc rows q c, Le q pr →
/// Eq Rat (clearBelow M pr pc rows q c) (M q c)`.
///
/// *Rows at or above the pivot row are untouched.* `clearBelow` starts the
/// sweep at `succ pr`, so `Le q pr` is `Lt q (succ pr)` and this is
/// [`declare_clear_below_aux_off`] at that cursor.
fn declare_clear_below_off(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
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
    let q_fv = d.fresh_fvar();
    let q = d.kernel().fvar(q_fv);
    let col_fv = d.fresh_fvar();
    let col = d.kernel().fvar(col_fv);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let hyp_ty = NatOps::le(d, q, pr);
    let swept = d.const_app(p.clear_below, &[m, pr, pc, rows]);
    let lhs = d.apply(swept, &[q, col]);
    let rhs = d.apply(m, &[q, col]);
    let stmt = req(d, lhs, rhs);

    let lt_succ_of_le = d.prelude().lt_succ_of_le;
    let in_range = d.lemma(lt_succ_of_le, &[q, pr, h]);
    let spr = d.succ(pr);
    let aux = d.lemma(p.clear_below_aux_off, &[pr, pc, rows, q, col, rows, m, spr]);
    let body = d.apply(aux, &[in_range]);
    let proof = d.lam_fv(h_fv, hyp_ty, body);

    let ty = {
        let over_h = d.pi_fv(h_fv, hyp_ty, stmt);
        let over_col = d.pi_fv(col_fv, nat, over_h);
        let over_q = d.pi_fv(q_fv, nat, over_col);
        let over_rows = d.pi_fv(rows_fv, nat, over_q);
        let over_pc = d.pi_fv(pc_fv, nat, over_rows);
        let over_pr = d.pi_fv(pr_fv, nat, over_pc);
        d.pi_fv(m_fv, mty, over_pr)
    };
    let value = {
        let over_col = d.lam_fv(col_fv, nat, proof);
        let over_q = d.lam_fv(q_fv, nat, over_col);
        let over_rows = d.lam_fv(rows_fv, nat, over_q);
        let over_pc = d.lam_fv(pc_fv, nat, over_rows);
        let over_pr = d.lam_fv(pr_fv, nat, over_pc);
        d.lam_fv(m_fv, mty, over_pr)
    };
    d.declare_theorem(p.clear_below_off, ty, value)
}

/// Admit `Rat.clearBelowAux_zero : ∀ pr pc rows q fuel M r, Lt pr r →
/// Le r q → Lt q rows → Lt q (Nat.add r fuel) → Not (Eq Rat (M pr pc) Rat.zero)
/// → Eq Rat (clearBelowAux pr pc rows fuel M r q pc) Rat.zero`.
///
/// The zero half. See the module note for what each hypothesis buys; the two
/// interesting branches are the `r = q` one, where
/// [`declare_clear_below_aux_off`] fixes the value the rest of the sweep leaves
/// alone and [`declare_add_neg_div_mul_cancel`] computes it, and the `Lt r q`
/// one, where the induction hypothesis fires after `Rat.rowAddMul_off` carries
/// the nonzero pivot across the rewrite.
fn declare_clear_below_aux_zero(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let mty = mat_ty(d);

    let pr_fv = d.fresh_fvar();
    let pr = d.kernel().fvar(pr_fv);
    let pc_fv = d.fresh_fvar();
    let pc = d.kernel().fvar(pc_fv);
    let rows_fv = d.fresh_fvar();
    let rows = d.kernel().fvar(rows_fv);
    let q_fv = d.fresh_fvar();
    let q = d.kernel().fvar(q_fv);
    let fuel_fv = d.fresh_fvar();
    let fuel = d.kernel().fvar(fuel_fv);

    // The five hypotheses, at an arbitrary matrix, cursor and fuel.
    let hyps = |d: &mut IntDev<'_>, m: ExprId, r: ExprId, x: ExprId| -> [ExprId; 5] {
        let h1 = NatOps::lt(d, pr, r);
        let h2 = NatOps::le(d, r, q);
        let h3 = NatOps::lt(d, q, rows);
        let bound = NatOps::add(d, r, x);
        let h4 = NatOps::lt(d, q, bound);
        let pivot = d.apply(m, &[pr, pc]);
        let h5 = ne_zero(d, p, pivot);
        [h1, h2, h3, h4, h5]
    };

    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        let swept = d.const_app(p.clear_below_aux, &[pr, pc, rows, x, m, r]);
        let lhs = d.apply(swept, &[q, pc]);
        let zero_r = rzero(d, p);
        let concl = req(d, lhs, zero_r);
        let [h1, h2, h3, h4, h5] = hyps(d, m, r, x);
        let after5 = d.arrow(h5, concl);
        let after4 = d.arrow(h4, after5);
        let after3 = d.arrow(h3, after4);
        let after2 = d.arrow(h2, after3);
        let body = d.arrow(h1, after2);
        let over_r = d.pi_fv(r_fv, nat, body);
        d.pi_fv(m_fv, mty, over_r)
    };
    let stmt = motive(d, fuel);

    // `λ h1 h2 h3 h4 h5, body` at an arbitrary matrix, cursor and fuel.
    let bind_hyps = |d: &mut IntDev<'_>,
                     m: ExprId,
                     r: ExprId,
                     x: ExprId,
                     body: &dyn Fn(&mut IntDev<'_>, [ExprId; 5]) -> ExprId|
     -> ExprId {
        let [t1, t2, t3, t4, t5] = hyps(d, m, r, x);
        let f1 = d.fresh_fvar();
        let f2 = d.fresh_fvar();
        let f3 = d.fresh_fvar();
        let f4 = d.fresh_fvar();
        let f5 = d.fresh_fvar();
        let v1 = d.kernel().fvar(f1);
        let v2 = d.kernel().fvar(f2);
        let v3 = d.kernel().fvar(f3);
        let v4 = d.kernel().fvar(f4);
        let v5 = d.kernel().fvar(f5);
        let inner = body(d, [v1, v2, v3, v4, v5]);
        let l5 = d.lam_fv(f5, t5, inner);
        let l4 = d.lam_fv(f4, t4, l5);
        let l3 = d.lam_fv(f3, t3, l4);
        let l2 = d.lam_fv(f2, t2, l3);
        d.lam_fv(f1, t1, l2)
    };

    let base = |d: &mut IntDev<'_>| -> ExprId {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        let zero_n = d.zero();
        let body = bind_hyps(d, m, r, zero_n, &|d, hs| {
            // `Lt q (r + 0)` is `Lt q r`; with `Le r q` that is `Lt q q`.
            let lt_of_lt_of_le = d.prelude().lt_of_lt_of_le;
            let lt_irrefl = d.prelude().lt_irrefl;
            let self_lt = d.lemma(lt_of_lt_of_le, &[q, r, q, hs[3], hs[1]]);
            let contradiction = d.lemma(lt_irrefl, &[q, self_lt]);
            let swept = d.const_app(p.clear_below_aux, &[pr, pc, rows, zero_n, m, r]);
            let lhs = d.apply(swept, &[q, pc]);
            let zero_r = rzero(d, p);
            let goal = req(d, lhs, zero_r);
            absurd(d, goal, contradiction)
        });
        let over_r = d.lam_fv(r_fv, nat, body);
        d.lam_fv(m_fv, mty, over_r)
    };

    let step = |d: &mut IntDev<'_>, n: ExprId, ih: ExprId| -> ExprId {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        let sn = d.succ(n);

        let body = bind_hyps(d, m, r, sn, &|d, hs| {
            let here = d.apply(m, &[r, pc]);
            let pivot = d.apply(m, &[pr, pc]);
            let ratio = rdiv(d, p, here, pivot);
            let factor = rneg(d, ratio);
            let updated = rrow_add_mul(d, p, r, pr, factor, m);
            let sr = d.succ(r);
            let recursed = d.const_app(p.clear_below_aux, &[pr, pc, rows, n, updated, sr]);
            let oor = NatOps::ble(d, rows, r);

            let shape = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
                let sel = bool_select_at(d, mty, x, m, recursed);
                let lhs = d.apply(sel, &[q, pc]);
                let zero_r = rzero(d, p);
                req(d, lhs, zero_r)
            };
            let goal = shape(d, oor);

            let true_ = d.bool_true();
            let false_ = d.bool_false();
            let h_true_ty = d.bool_eq(oor, true_);
            let h_false_ty = d.bool_eq(oor, false_);

            // `Nat.ble rows r = true` says the sweep stopped, but `Le r q` and
            // `Lt q rows` put `r` strictly inside the range. Refuted.
            let left_minor = {
                let ht_fv = d.fresh_fvar();
                let ht = d.kernel().fvar(ht_fv);
                let le_of_ble_eq_true = d.prelude().le_of_ble_eq_true;
                let lt_of_le_of_lt = d.prelude().lt_of_le_of_lt;
                let lt_of_lt_of_le = d.prelude().lt_of_lt_of_le;
                let lt_irrefl = d.prelude().lt_irrefl;
                let rows_le_r = d.lemma(le_of_ble_eq_true, &[rows, r, ht]);
                let r_lt_rows = d.lemma(lt_of_le_of_lt, &[r, q, rows, hs[1], hs[2]]);
                let self_lt = d.lemma(lt_of_lt_of_le, &[r, rows, r, r_lt_rows, rows_le_r]);
                let contradiction = d.lemma(lt_irrefl, &[r, self_lt]);
                let target = shape(d, true_);
                let refl_case = absurd(d, target, contradiction);
                let motive_x = d.bool_eq_motive(true_, &shape);
                let ht_sym = d.bool_symm(oor, true_, ht);
                let inner = d.bool_transport(true_, motive_x, refl_case, oor, ht_sym);
                d.lam_fv(ht_fv, h_true_ty, inner)
            };

            let right_minor = {
                let hf_fv = d.fresh_fvar();
                let hf = d.kernel().fvar(hf_fv);
                let false_goal = shape(d, false_);

                // The pivot entry survives the rewrite: `pr < r`, so row `pr`
                // is not the row this step changed.
                let pivot_off = {
                    let hbeq = beq_false_of_lt(d, pr, r, hs[0]);
                    d.lemma(p.row_add_mul_off, &[r, pr, factor, m, pr, hbeq, pc])
                };
                let updated_pivot = d.apply(updated, &[pr, pc]);
                let carried = {
                    // The BINDER is the equation, not its negation: this
                    // lambda IS the `Not`, so binding `he` at `Not (…)` would
                    // build `Not (Not (…))` and the kernel would reject it —
                    // which is exactly what it did on the first attempt.
                    let zero_r = rzero(d, p);
                    let assumed = req(d, updated_pivot, zero_r);
                    let he_fv = d.fresh_fvar();
                    let he = d.kernel().fvar(he_fv);
                    let back = rsymm(d, updated_pivot, pivot, pivot_off);
                    let chained = rtrans(d, pivot, updated_pivot, zero_r, back, he);
                    let contradiction = d.apply(hs[4], &[chained]);
                    d.lam_fv(he_fv, assumed, contradiction)
                };

                let lt_or_eq_of_le = d.prelude().lt_or_eq_of_le;
                let split = d.lemma(lt_or_eq_of_le, &[r, q, hs[1]]);
                let lt_ty = NatOps::lt(d, r, q);
                let eq_ty = d.eq(r, q);

                // `r < q`: the target row is still below, so recurse.
                let below = {
                    let hlt_fv = d.fresh_fvar();
                    let hlt = d.kernel().fvar(hlt_fv);
                    let le_trans = d.prelude().le_trans;
                    let le_succ = d.prelude().le_succ;
                    let spr = d.succ(pr);
                    let up = d.lemma(le_succ, &[r]);
                    let a1 = d.lemma(le_trans, &[spr, r, sr, hs[0], up]);
                    let a4 = {
                        let succ_add = d.prelude().succ_add;
                        let shifted = d.lemma(succ_add, &[r, n]);
                        let left = NatOps::add(d, sr, n);
                        let inner = NatOps::add(d, r, n);
                        let right = d.succ(inner);
                        let back = NatOps::symm(d, left, right, shifted);
                        nat_rewrite_prop(d, right, left, back, hs[3], &|d, t| NatOps::lt(d, q, t))
                    };
                    let applied = d.apply(ih, &[updated, sr, a1, hlt, hs[2], a4, carried]);
                    d.lam_fv(hlt_fv, lt_ty, applied)
                };

                // `r = q`: this step clears the target row, and nothing after
                // it touches row `r` again.
                let here_row = {
                    let he_fv = d.fresh_fvar();
                    let he = d.kernel().fvar(he_fv);
                    let lt_succ_self = d.prelude().lt_succ_self;
                    let stays = d.lemma(lt_succ_self, &[r]);
                    let off = d.lemma(
                        p.clear_below_aux_off,
                        &[pr, pc, rows, r, pc, n, updated, sr, stays],
                    );
                    let at_r = d.lemma(p.row_add_mul_at, &[r, pr, factor, m, pc]);
                    let arith = d.lemma(p.add_neg_div_mul_cancel, &[here, pivot, hs[4]]);
                    let recursed_at_r = d.apply(recursed, &[r, pc]);
                    let updated_at_r = d.apply(updated, &[r, pc]);
                    let scaled = rmul(d, factor, pivot);
                    let sum = radd(d, here, scaled);
                    let zero_r = rzero(d, p);
                    let (_, at_row) = rchain(
                        d,
                        recursed_at_r,
                        &[(updated_at_r, off), (sum, at_r), (zero_r, arith)],
                    );
                    let moved = nat_rewrite_prop(d, r, q, he, at_row, &|d, t| {
                        let lhs = d.apply(recursed, &[t, pc]);
                        let zero_r = rzero(d, p);
                        req(d, lhs, zero_r)
                    });
                    d.lam_fv(he_fv, eq_ty, moved)
                };

                let refl_case = or_cases(d, lt_ty, eq_ty, false_goal, below, here_row, split);
                let motive_x = d.bool_eq_motive(false_, &shape);
                let hf_sym = d.bool_symm(oor, false_, hf);
                let inner = d.bool_transport(false_, motive_x, refl_case, oor, hf_sym);
                d.lam_fv(hf_fv, h_false_ty, inner)
            };

            let bool_split = bool_cases(d, oor);
            or_cases(
                d,
                h_true_ty,
                h_false_ty,
                goal,
                left_minor,
                right_minor,
                bool_split,
            )
        });

        let over_r = d.lam_fv(r_fv, nat, body);
        d.lam_fv(m_fv, mty, over_r)
    };

    let proof = d.induct(&motive, &base, &step, fuel);

    let ty = {
        let over_fuel = d.pi_fv(fuel_fv, nat, stmt);
        let over_q = d.pi_fv(q_fv, nat, over_fuel);
        let over_rows = d.pi_fv(rows_fv, nat, over_q);
        let over_pc = d.pi_fv(pc_fv, nat, over_rows);
        d.pi_fv(pr_fv, nat, over_pc)
    };
    let value = {
        let over_fuel = d.lam_fv(fuel_fv, nat, proof);
        let over_q = d.lam_fv(q_fv, nat, over_fuel);
        let over_rows = d.lam_fv(rows_fv, nat, over_q);
        let over_pc = d.lam_fv(pc_fv, nat, over_rows);
        d.lam_fv(pr_fv, nat, over_pc)
    };
    d.declare_theorem(p.clear_below_aux_zero, ty, value)
}

/// Admit `Rat.clearBelow_zero : ∀ M pr pc rows q, Lt pr q → Lt q rows →
/// Not (Eq Rat (M pr pc) Rat.zero) →
/// Eq Rat (clearBelow M pr pc rows q pc) Rat.zero`.
///
/// The statement ADR-1554 asks obligation 3 for. `clearBelow` hands the loop
/// `rows` units of fuel starting at `succ pr`, so the fuel bound
/// `Lt q (succ pr + rows)` follows from `Lt q rows` by `Nat.le_add_right` and
/// one `Nat.add_comm`.
fn declare_clear_below_zero(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
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
    let q_fv = d.fresh_fvar();
    let q = d.kernel().fvar(q_fv);

    let h1_fv = d.fresh_fvar();
    let h1 = d.kernel().fvar(h1_fv);
    let h2_fv = d.fresh_fvar();
    let h2 = d.kernel().fvar(h2_fv);
    let h3_fv = d.fresh_fvar();
    let h3 = d.kernel().fvar(h3_fv);

    let t1 = NatOps::lt(d, pr, q);
    let t2 = NatOps::lt(d, q, rows);
    let pivot = d.apply(m, &[pr, pc]);
    let t3 = ne_zero(d, p, pivot);

    let swept = d.const_app(p.clear_below, &[m, pr, pc, rows]);
    let lhs = d.apply(swept, &[q, pc]);
    let zero_r = rzero(d, p);
    let stmt = req(d, lhs, zero_r);

    let spr = d.succ(pr);
    let lt_succ_self = d.prelude().lt_succ_self;
    let a1 = d.lemma(lt_succ_self, &[pr]);
    let a4 = {
        let le_add_right = d.prelude().le_add_right;
        let add_comm = d.prelude().add_comm;
        let lt_of_lt_of_le = d.prelude().lt_of_lt_of_le;
        let grown = d.lemma(le_add_right, &[rows, spr]);
        let right_sum = NatOps::add(d, rows, spr);
        let left_sum = NatOps::add(d, spr, rows);
        let flip = d.lemma(add_comm, &[rows, spr]);
        let moved = nat_rewrite_prop(d, right_sum, left_sum, flip, grown, &|d, t| {
            NatOps::le(d, rows, t)
        });
        d.lemma(lt_of_lt_of_le, &[q, rows, left_sum, h2, moved])
    };
    let aux = d.lemma(p.clear_below_aux_zero, &[pr, pc, rows, q, rows, m, spr]);
    let body = d.apply(aux, &[a1, h1, h2, a4, h3]);
    let proof = {
        let l3 = d.lam_fv(h3_fv, t3, body);
        let l2 = d.lam_fv(h2_fv, t2, l3);
        d.lam_fv(h1_fv, t1, l2)
    };

    let ty = {
        let f3 = d.pi_fv(h3_fv, t3, stmt);
        let f2 = d.pi_fv(h2_fv, t2, f3);
        let f1 = d.pi_fv(h1_fv, t1, f2);
        let over_q = d.pi_fv(q_fv, nat, f1);
        let over_rows = d.pi_fv(rows_fv, nat, over_q);
        let over_pc = d.pi_fv(pc_fv, nat, over_rows);
        let over_pr = d.pi_fv(pr_fv, nat, over_pc);
        d.pi_fv(m_fv, mty, over_pr)
    };
    let value = {
        let over_q = d.lam_fv(q_fv, nat, proof);
        let over_rows = d.lam_fv(rows_fv, nat, over_q);
        let over_pc = d.lam_fv(pc_fv, nat, over_rows);
        let over_pr = d.lam_fv(pr_fv, nat, over_pc);
        d.lam_fv(m_fv, mty, over_pr)
    };
    d.declare_theorem(p.clear_below_zero, ty, value)
}

/// `∀ s, Le pr s → Lt s rows → Eq Rat (M s k) Rat.zero` — column `k` is zero
/// at every row from the pivot row down.
fn column_zero_from(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    m: ExprId,
    pr: ExprId,
    rows: ExprId,
    k: ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let s_fv = d.fresh_fvar();
    let s = d.kernel().fvar(s_fv);
    let lower = NatOps::le(d, pr, s);
    let upper = NatOps::lt(d, s, rows);
    let entry = d.apply(m, &[s, k]);
    let zero_r = rzero(d, p);
    let concl = req(d, entry, zero_r);
    let inner = d.arrow(upper, concl);
    let body = d.arrow(lower, inner);
    d.pi_fv(s_fv, nat, body)
}

/// Admit `Rat.clearBelowAux_preserves_zero : ∀ pr pc rows k M r q, Le pr r →
/// Le r q → Lt q rows → (∀ s, Le pr s → Lt s rows → Eq Rat (M s k) Rat.zero) →
/// Eq Rat (clearBelowAux pr pc rows fuel M r q k) Rat.zero`.
///
/// *A column that is already zero from the pivot row down STAYS zero.* This is
/// the clause the loop invariant carries about the columns to the left of the
/// cursor, and it is what makes a pivot step extend that range by one column
/// rather than destroying it.
///
/// **There is no fuel bound here**, and the contrast with
/// [`declare_clear_below_aux_zero`] is the point. That one needs `Lt q (r +
/// fuel)` because an exhausted sweep returns `M` untouched and the conclusion
/// is about a value the sweep was supposed to CREATE. Here the conclusion is
/// about a value the sweep is supposed to PRESERVE, so the exhausted answer
/// satisfies it directly — the base case and the out-of-range branch both close
/// from the hypothesis rather than being refuted.
///
/// Re-establishing the hypothesis at the rewritten matrix is the only work in
/// the step, and it splits on `Nat.beq s r` — a FREE split, because neither
/// branch's conclusion mentions the tested `Bool` (ADR-1562 §3). Off the
/// rewritten row `Rat.rowAddMul_off` applies; on it the entry is
/// `M r k + (-(…)) * M pr k`, and BOTH summands are zero by hypothesis, which
/// is why `Le pr r` is required rather than derived.
fn declare_clear_below_aux_preserves_zero(
    d: &mut IntDev<'_>,
    p: RatPrelude,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let mty = mat_ty(d);

    let pr_fv = d.fresh_fvar();
    let pr = d.kernel().fvar(pr_fv);
    let pc_fv = d.fresh_fvar();
    let pc = d.kernel().fvar(pc_fv);
    let rows_fv = d.fresh_fvar();
    let rows = d.kernel().fvar(rows_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let q_fv = d.fresh_fvar();
    let q = d.kernel().fvar(q_fv);
    let fuel_fv = d.fresh_fvar();
    let fuel = d.kernel().fvar(fuel_fv);

    let hyps = |d: &mut IntDev<'_>, m: ExprId, r: ExprId| -> [ExprId; 4] {
        let h1 = NatOps::le(d, pr, r);
        let h2 = NatOps::le(d, r, q);
        let h3 = NatOps::lt(d, q, rows);
        let h4 = column_zero_from(d, p, m, pr, rows, k);
        [h1, h2, h3, h4]
    };

    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        let swept = d.const_app(p.clear_below_aux, &[pr, pc, rows, x, m, r]);
        let lhs = d.apply(swept, &[q, k]);
        let zero_r = rzero(d, p);
        let concl = req(d, lhs, zero_r);
        let [h1, h2, h3, h4] = hyps(d, m, r);
        let after4 = d.arrow(h4, concl);
        let after3 = d.arrow(h3, after4);
        let after2 = d.arrow(h2, after3);
        let body = d.arrow(h1, after2);
        let over_r = d.pi_fv(r_fv, nat, body);
        d.pi_fv(m_fv, mty, over_r)
    };
    let stmt = motive(d, fuel);

    let bind_hyps = |d: &mut IntDev<'_>,
                     m: ExprId,
                     r: ExprId,
                     body: &dyn Fn(&mut IntDev<'_>, [ExprId; 4]) -> ExprId|
     -> ExprId {
        let [t1, t2, t3, t4] = hyps(d, m, r);
        let f1 = d.fresh_fvar();
        let f2 = d.fresh_fvar();
        let f3 = d.fresh_fvar();
        let f4 = d.fresh_fvar();
        let v1 = d.kernel().fvar(f1);
        let v2 = d.kernel().fvar(f2);
        let v3 = d.kernel().fvar(f3);
        let v4 = d.kernel().fvar(f4);
        let inner = body(d, [v1, v2, v3, v4]);
        let l4 = d.lam_fv(f4, t4, inner);
        let l3 = d.lam_fv(f3, t3, l4);
        let l2 = d.lam_fv(f2, t2, l3);
        d.lam_fv(f1, t1, l2)
    };

    // The hypothesis, read at the target row `q`: `Le pr q` comes from
    // `Le pr r` and `Le r q`.
    let at_target = |d: &mut IntDev<'_>, hs: [ExprId; 4], r: ExprId| -> ExprId {
        let le_trans = d.prelude().le_trans;
        let pr_le_q = d.lemma(le_trans, &[pr, r, q, hs[0], hs[1]]);
        d.apply(hs[3], &[q, pr_le_q, hs[2]])
    };

    let base = |d: &mut IntDev<'_>| -> ExprId {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        let body = bind_hyps(d, m, r, &|d, hs| at_target(d, hs, r));
        let over_r = d.lam_fv(r_fv, nat, body);
        d.lam_fv(m_fv, mty, over_r)
    };

    let step = |d: &mut IntDev<'_>, n: ExprId, ih: ExprId| -> ExprId {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);

        let body = bind_hyps(d, m, r, &|d, hs| {
            let here = d.apply(m, &[r, pc]);
            let pivot = d.apply(m, &[pr, pc]);
            let ratio = rdiv(d, p, here, pivot);
            let factor = rneg(d, ratio);
            let updated = rrow_add_mul(d, p, r, pr, factor, m);
            let sr = d.succ(r);
            let recursed = d.const_app(p.clear_below_aux, &[pr, pc, rows, n, updated, sr]);
            let oor = NatOps::ble(d, rows, r);
            let zero_r = rzero(d, p);

            let shape = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
                let sel = bool_select_at(d, mty, x, m, recursed);
                let lhs = d.apply(sel, &[q, k]);
                let zero_r = rzero(d, p);
                req(d, lhs, zero_r)
            };
            let goal = shape(d, oor);

            let true_ = d.bool_true();
            let false_ = d.bool_false();
            let h_true_ty = d.bool_eq(oor, true_);
            let h_false_ty = d.bool_eq(oor, false_);

            // The sweep stopped: the answer is `M q k`, which the hypothesis
            // already says is zero. Nothing to refute.
            let left_minor = {
                let ht_fv = d.fresh_fvar();
                let ht = d.kernel().fvar(ht_fv);
                let refl_case = at_target(d, hs, r);
                let motive_x = d.bool_eq_motive(true_, &shape);
                let ht_sym = d.bool_symm(oor, true_, ht);
                let inner = d.bool_transport(true_, motive_x, refl_case, oor, ht_sym);
                d.lam_fv(ht_fv, h_true_ty, inner)
            };

            let right_minor = {
                let hf_fv = d.fresh_fvar();
                let hf = d.kernel().fvar(hf_fv);

                // `r` and `pr` are both strictly inside the row count.
                let lt_of_le_of_lt = d.prelude().lt_of_le_of_lt;
                let r_lt_rows = d.lemma(lt_of_le_of_lt, &[r, q, rows, hs[1], hs[2]]);
                let pr_lt_rows = d.lemma(lt_of_le_of_lt, &[pr, r, rows, hs[0], r_lt_rows]);

                // The rewritten row is still zero in column `k`, because both
                // summands are.
                let rewritten_row_zero = {
                    let le_refl = d.prelude().le_refl_thm;
                    let pr_le_pr = d.lemma(le_refl, &[pr]);
                    let row_zero = d.apply(hs[3], &[r, hs[0], r_lt_rows]);
                    let pivot_row_zero = d.apply(hs[3], &[pr, pr_le_pr, pr_lt_rows]);
                    let at_r = d.lemma(p.row_add_mul_at, &[r, pr, factor, m, k]);
                    let here_k = d.apply(m, &[r, k]);
                    let pivot_k = d.apply(m, &[pr, k]);
                    let scaled = rmul(d, factor, pivot_k);
                    let sum = radd(d, here_k, scaled);
                    let scaled_zero = rmul(d, factor, zero_r);
                    let sum_zeroed = radd(d, zero_r, scaled_zero);
                    let left_step = rcongr(d, here_k, zero_r, row_zero, &|d, t| {
                        let pivot_k_inner = d.apply(m, &[pr, k]);
                        let scaled_inner = rmul(d, factor, pivot_k_inner);
                        radd(d, t, scaled_inner)
                    });
                    let right_step = rcongr(d, pivot_k, zero_r, pivot_row_zero, &|d, t| {
                        let scaled_inner = rmul(d, factor, t);
                        radd(d, zero_r, scaled_inner)
                    });
                    let sum_partly = radd(d, zero_r, scaled);
                    let mul_zero = d.lemma(p.mul_zero, &[factor]);
                    let collapse =
                        rcongr(d, scaled_zero, zero_r, mul_zero, &|d, t| radd(d, zero_r, t));
                    let sum_final = radd(d, zero_r, zero_r);
                    let add_zero = d.lemma(p.add_zero, &[zero_r]);
                    let updated_at_r = d.apply(updated, &[r, k]);
                    let (_, chained) = rchain(
                        d,
                        updated_at_r,
                        &[
                            (sum, at_r),
                            (sum_partly, left_step),
                            (sum_zeroed, right_step),
                            (sum_final, collapse),
                            (zero_r, add_zero),
                        ],
                    );
                    chained
                };

                // ... and every OTHER row in range is untouched, so the whole
                // hypothesis is re-established at the rewritten matrix.
                let carried = {
                    let s_fv = d.fresh_fvar();
                    let s = d.kernel().fvar(s_fv);
                    let lower = NatOps::le(d, pr, s);
                    let upper = NatOps::lt(d, s, rows);
                    let hs1_fv = d.fresh_fvar();
                    let hs1 = d.kernel().fvar(hs1_fv);
                    let hs2_fv = d.fresh_fvar();
                    let hs2 = d.kernel().fvar(hs2_fv);

                    let updated_at_s = d.apply(updated, &[s, k]);
                    let target = req(d, updated_at_s, zero_r);

                    let test = NatOps::beq(d, s, r);
                    let is_true = d.bool_eq(test, true_);
                    let is_false = d.bool_eq(test, false_);

                    let on_true = {
                        let hb_fv = d.fresh_fvar();
                        let hb = d.kernel().fvar(hb_fv);
                        let eq_of_beq = d.prelude().eq_of_beq_eq_true;
                        let s_eq_r = d.lemma(eq_of_beq, &[s, r, hb]);
                        let back = NatOps::symm(d, s, r, s_eq_r);
                        let moved = nat_rewrite_prop(d, r, s, back, rewritten_row_zero, &|d, t| {
                            let at_t = d.apply(updated, &[t, k]);
                            let zero_inner = rzero(d, p);
                            req(d, at_t, zero_inner)
                        });
                        d.lam_fv(hb_fv, is_true, moved)
                    };
                    let on_false = {
                        let hb_fv = d.fresh_fvar();
                        let hb = d.kernel().fvar(hb_fv);
                        let off = d.lemma(p.row_add_mul_off, &[r, pr, factor, m, s, hb, k]);
                        let original = d.apply(hs[3], &[s, hs1, hs2]);
                        let at_s = d.apply(m, &[s, k]);
                        let joined = rtrans(d, updated_at_s, at_s, zero_r, off, original);
                        d.lam_fv(hb_fv, is_false, joined)
                    };

                    let split = bool_cases(d, test);
                    let chosen = or_cases(d, is_true, is_false, target, on_true, on_false, split);
                    let with_hs2 = d.lam_fv(hs2_fv, upper, chosen);
                    let with_hs1 = d.lam_fv(hs1_fv, lower, with_hs2);
                    d.lam_fv(s_fv, nat, with_hs1)
                };

                let false_goal = shape(d, false_);
                let lt_or_eq_of_le = d.prelude().lt_or_eq_of_le;
                let split = d.lemma(lt_or_eq_of_le, &[r, q, hs[1]]);
                let lt_ty = NatOps::lt(d, r, q);
                let eq_ty = d.eq(r, q);

                let below = {
                    let hlt_fv = d.fresh_fvar();
                    let hlt = d.kernel().fvar(hlt_fv);
                    let le_trans = d.prelude().le_trans;
                    let le_succ = d.prelude().le_succ;
                    let up = d.lemma(le_succ, &[r]);
                    let a1 = d.lemma(le_trans, &[pr, r, sr, hs[0], up]);
                    let applied = d.apply(ih, &[updated, sr, a1, hlt, hs[2], carried]);
                    d.lam_fv(hlt_fv, lt_ty, applied)
                };
                let here_row = {
                    let he_fv = d.fresh_fvar();
                    let he = d.kernel().fvar(he_fv);
                    let lt_succ_self = d.prelude().lt_succ_self;
                    let stays = d.lemma(lt_succ_self, &[r]);
                    let off = d.lemma(
                        p.clear_below_aux_off,
                        &[pr, pc, rows, r, k, n, updated, sr, stays],
                    );
                    let recursed_at_r = d.apply(recursed, &[r, k]);
                    let updated_at_r = d.apply(updated, &[r, k]);
                    let joined = rtrans(
                        d,
                        recursed_at_r,
                        updated_at_r,
                        zero_r,
                        off,
                        rewritten_row_zero,
                    );
                    let moved = nat_rewrite_prop(d, r, q, he, joined, &|d, t| {
                        let lhs = d.apply(recursed, &[t, k]);
                        let zero_inner = rzero(d, p);
                        req(d, lhs, zero_inner)
                    });
                    d.lam_fv(he_fv, eq_ty, moved)
                };

                let refl_case = or_cases(d, lt_ty, eq_ty, false_goal, below, here_row, split);
                let motive_x = d.bool_eq_motive(false_, &shape);
                let hf_sym = d.bool_symm(oor, false_, hf);
                let inner = d.bool_transport(false_, motive_x, refl_case, oor, hf_sym);
                d.lam_fv(hf_fv, h_false_ty, inner)
            };

            let bool_split = bool_cases(d, oor);
            or_cases(
                d,
                h_true_ty,
                h_false_ty,
                goal,
                left_minor,
                right_minor,
                bool_split,
            )
        });

        let over_r = d.lam_fv(r_fv, nat, body);
        d.lam_fv(m_fv, mty, over_r)
    };

    let proof = d.induct(&motive, &base, &step, fuel);

    let ty = {
        let over_fuel = d.pi_fv(fuel_fv, nat, stmt);
        let over_q = d.pi_fv(q_fv, nat, over_fuel);
        let over_k = d.pi_fv(k_fv, nat, over_q);
        let over_rows = d.pi_fv(rows_fv, nat, over_k);
        let over_pc = d.pi_fv(pc_fv, nat, over_rows);
        d.pi_fv(pr_fv, nat, over_pc)
    };
    let value = {
        let over_fuel = d.lam_fv(fuel_fv, nat, proof);
        let over_q = d.lam_fv(q_fv, nat, over_fuel);
        let over_k = d.lam_fv(k_fv, nat, over_q);
        let over_rows = d.lam_fv(rows_fv, nat, over_k);
        let over_pc = d.lam_fv(pc_fv, nat, over_rows);
        d.lam_fv(pr_fv, nat, over_pc)
    };
    d.declare_theorem(p.clear_below_aux_preserves_zero, ty, value)
}

/// Admit `Rat.clearBelow_preserves_zero : ∀ M pr pc rows k q, Lt pr q →
/// Lt q rows → (∀ s, Le pr s → Lt s rows → Eq Rat (M s k) Rat.zero) →
/// Eq Rat (clearBelow M pr pc rows q k) Rat.zero`.
///
/// [`declare_clear_below_aux_preserves_zero`] at the cursor `succ pr`, where
/// `Le pr (succ pr)` is `Nat.le_succ` and `Le (succ pr) q` is the hypothesis
/// `Lt pr q`. No fuel bound is needed, so unlike
/// [`declare_clear_below_zero`] this wrapper spends no arithmetic at all.
fn declare_clear_below_preserves_zero(
    d: &mut IntDev<'_>,
    p: RatPrelude,
) -> Result<(), KernelError> {
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
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let q_fv = d.fresh_fvar();
    let q = d.kernel().fvar(q_fv);

    let t1 = NatOps::lt(d, pr, q);
    let t2 = NatOps::lt(d, q, rows);
    let t3 = column_zero_from(d, p, m, pr, rows, k);

    let swept = d.const_app(p.clear_below, &[m, pr, pc, rows]);
    let lhs = d.apply(swept, &[q, k]);
    let zero_r = rzero(d, p);
    let concl = req(d, lhs, zero_r);

    let h1_fv = d.fresh_fvar();
    let h1 = d.kernel().fvar(h1_fv);
    let h2_fv = d.fresh_fvar();
    let h2 = d.kernel().fvar(h2_fv);
    let h3_fv = d.fresh_fvar();
    let h3 = d.kernel().fvar(h3_fv);

    let spr = d.succ(pr);
    let le_succ = d.prelude().le_succ;
    let a1 = d.lemma(le_succ, &[pr]);
    let aux = d.lemma(
        p.clear_below_aux_preserves_zero,
        &[pr, pc, rows, k, q, rows, m, spr],
    );
    let body = d.apply(aux, &[a1, h1, h2, h3]);
    let proof = {
        let l3 = d.lam_fv(h3_fv, t3, body);
        let l2 = d.lam_fv(h2_fv, t2, l3);
        d.lam_fv(h1_fv, t1, l2)
    };

    let ty = {
        let f3 = d.pi_fv(h3_fv, t3, concl);
        let f2 = d.pi_fv(h2_fv, t2, f3);
        let f1 = d.pi_fv(h1_fv, t1, f2);
        let over_q = d.pi_fv(q_fv, nat, f1);
        let over_k = d.pi_fv(k_fv, nat, over_q);
        let over_rows = d.pi_fv(rows_fv, nat, over_k);
        let over_pc = d.pi_fv(pc_fv, nat, over_rows);
        let over_pr = d.pi_fv(pr_fv, nat, over_pc);
        d.pi_fv(m_fv, mty, over_pr)
    };
    let value = {
        let over_q = d.lam_fv(q_fv, nat, proof);
        let over_k = d.lam_fv(k_fv, nat, over_q);
        let over_rows = d.lam_fv(rows_fv, nat, over_k);
        let over_pc = d.lam_fv(pc_fv, nat, over_rows);
        let over_pr = d.lam_fv(pr_fv, nat, over_pc);
        d.lam_fv(m_fv, mty, over_pr)
    };
    d.declare_theorem(p.clear_below_preserves_zero, ty, value)
}
