//! What `Rat.leadingIndex` ANSWERS — the two characterizations the loop
//! invariant and `Rat.rank` both need (ADR-1554 obligation 4's first
//! prerequisite).
//!
//! ## Why a characterization and not an equation
//!
//! `Rat.leadingIndex` is a fuelled scan, so `echelon.rs` gives you its
//! defining unfolding and nothing else. Everything downstream wants the
//! opposite direction: *given what the row LOOKS like, what does the scan
//! return?* Two shapes cover every use.
//!
//! ```text
//! Rat.leadingIndex_eq_of_first_nonzero : ∀ M r cols j, Lt j cols →
//!   (∀ k, Lt k j → M r k = 0) → Not (M r j = 0) →
//!     leadingIndex M r cols = j
//! Rat.leadingIndex_eq_cols_of_zero_row : ∀ M r cols,
//!   (∀ k, Lt k cols → M r k = 0) → leadingIndex M r cols = cols
//! ```
//!
//! The first is what a freshly-pivoted row satisfies: the invariant knows the
//! row is zero left of the pivot column (that is the clause `echelonAux`
//! maintains) and nonzero AT it (obligation 2's value half), and those two
//! facts are exactly this lemma's hypotheses. The second is what every row
//! below the last pivot satisfies at exit, and `cols` is the answer
//! `Rat.echelonStepOk` reads as "this row is zero" (ADR-1554 §3).
//!
//! ## The `Nat.ble cols c = false` branch is where the strict bridge is spent
//!
//! ADR-1562 §4 recorded that `Nat` was owed `ble a b = false → Lt b a` in its
//! STRICT form, and named this file's kind of use as the third consumer. It is
//! spent once, in [`declare_leading_index_aux_eq_cols_of_zero`]: the scan's
//! `false` branch is the ONLY place the column index is known to be inside
//! `cols`, and the zero-range hypothesis needs `Lt k cols` before it will
//! answer. The non-strict `Le` that `pivot_bound.rs`'s `le_total` route
//! produces cannot be used there.
//!
//! ## Which leaves do work
//!
//! Both inductions have four leaves and in each only one of them is the
//! interesting case, but they are DIFFERENT leaves, which is the useful
//! observation:
//!
//! - in the first-nonzero lemma the `isZeroB = false` leaf is the one that
//!   CLOSES (the scan stopped where it should have), and the two exhaustion
//!   leaves are refuted from the range hypotheses;
//! - in the zero-row lemma both exhaustion leaves close by `Eq.refl` — the
//!   scan's answer when it gives up is `cols`, which is the conclusion — and
//!   the `isZeroB = false` leaf is the one REFUTED, because a nonzero entry
//!   inside the range contradicts the hypothesis.
//!
//! So a fuel scan's exhaustion answer being the same as the conclusion turns
//! two obligations into `refl`, and that is the whole reason ADR-1554 §2 chose
//! `cols` for a zero row rather than an out-of-band sentinel.

use super::RatPrelude;
use super::echelon::{bool_select_at, ris_zero_b};
use super::matrix_det::mat_ty;
use super::ops::{nat_rewrite_prop, req, rzero};
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
pub(super) fn declare_leading_index_facts(
    d: &mut IntDev<'_>,
    p: RatPrelude,
) -> Result<(), KernelError> {
    declare_leading_index_aux_eq_of_first_nonzero(d, p)?;
    declare_leading_index_eq_of_first_nonzero(d, p)?;
    declare_leading_index_aux_eq_cols_of_zero(d, p)?;
    declare_leading_index_eq_cols_of_zero_row(d, p)?;
    Ok(())
}

/// `Eq Rat (M r k) Rat.zero`.
fn entry_zero(d: &mut IntDev<'_>, p: RatPrelude, m: ExprId, r: ExprId, k: ExprId) -> ExprId {
    let entry = d.apply(m, &[r, k]);
    let zero_r = rzero(d, p);
    req(d, entry, zero_r)
}

/// `Not (Eq Rat (M r k) Rat.zero)`.
fn entry_nonzero(d: &mut IntDev<'_>, p: RatPrelude, m: ExprId, r: ExprId, k: ExprId) -> ExprId {
    let equation = entry_zero(d, p, m, r, k);
    d.not(equation)
}

/// `∀ k, Le lo k → Lt k hi → Eq Rat (M r k) Rat.zero` — the half-open range in
/// which row `r` is known to be zero.
fn zero_between(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    m: ExprId,
    r: ExprId,
    lo: ExprId,
    hi: ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let lower = NatOps::le(d, lo, k);
    let upper = NatOps::lt(d, k, hi);
    let concl = entry_zero(d, p, m, r, k);
    let inner = d.arrow(upper, concl);
    let body = d.arrow(lower, inner);
    d.pi_fv(k_fv, nat, body)
}

/// Weaken `h : ∀ k, Le lo k → Lt k hi → …` to the same statement at `succ lo`.
fn zero_between_shift(d: &mut IntDev<'_>, lo: ExprId, hi: ExprId, h: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let slo = d.succ(lo);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let lower = NatOps::le(d, slo, k);
    let upper = NatOps::lt(d, k, hi);
    let hk1_fv = d.fresh_fvar();
    let hk1 = d.kernel().fvar(hk1_fv);
    let hk2_fv = d.fresh_fvar();
    let hk2 = d.kernel().fvar(hk2_fv);

    let le_succ = d.prelude().le_succ;
    let le_trans = d.prelude().le_trans;
    let step_up = d.lemma(le_succ, &[lo]);
    let widened = d.lemma(le_trans, &[lo, slo, k, step_up, hk1]);
    let applied = d.apply(h, &[k, widened, hk2]);

    let with_hk2 = d.lam_fv(hk2_fv, upper, applied);
    let with_hk1 = d.lam_fv(hk1_fv, lower, with_hk2);
    d.lam_fv(k_fv, nat, with_hk1)
}

/// Admit `Rat.leadingIndexAux_eq_of_first_nonzero : ∀ M r cols j c fuel,
/// Le c j → Lt j cols → Lt j (Nat.add c fuel) →
/// (∀ k, Le c k → Lt k j → Eq Rat (M r k) Rat.zero) →
/// Not (Eq Rat (M r j) Rat.zero) →
/// Eq Nat (leadingIndexAux M r cols fuel c) j`.
///
/// The scan started at `c`, everything in `[c, j)` is zero and `(r, j)` is
/// not, so the scan stops exactly at `j`. `c` is generalised inside the motive
/// because the step recurses at `succ c`; `M`, `r`, `cols` and the target `j`
/// are fixed.
fn declare_leading_index_aux_eq_of_first_nonzero(
    d: &mut IntDev<'_>,
    p: RatPrelude,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let mty = mat_ty(d);

    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let r_fv = d.fresh_fvar();
    let r = d.kernel().fvar(r_fv);
    let cols_fv = d.fresh_fvar();
    let cols = d.kernel().fvar(cols_fv);
    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);
    let fuel_fv = d.fresh_fvar();
    let fuel = d.kernel().fvar(fuel_fv);

    let hyps = |d: &mut IntDev<'_>, c: ExprId, x: ExprId| -> [ExprId; 4] {
        let h1 = NatOps::le(d, c, j);
        let h2 = NatOps::lt(d, j, cols);
        let bound = NatOps::add(d, c, x);
        let h3 = NatOps::lt(d, j, bound);
        let h4 = zero_between(d, p, m, r, c, j);
        [h1, h2, h3, h4]
    };

    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let c_fv = d.fresh_fvar();
        let c = d.kernel().fvar(c_fv);
        let scanned = d.const_app(p.leading_index_aux, &[m, r, cols, x, c]);
        let concl = d.eq(scanned, j);
        let h5 = entry_nonzero(d, p, m, r, j);
        let tail = d.arrow(h5, concl);
        let [h1, h2, h3, h4] = hyps(d, c, x);
        let after4 = d.arrow(h4, tail);
        let after3 = d.arrow(h3, after4);
        let after2 = d.arrow(h2, after3);
        let body = d.arrow(h1, after2);
        d.pi_fv(c_fv, nat, body)
    };
    let stmt = motive(d, fuel);

    let bind_hyps = |d: &mut IntDev<'_>,
                     c: ExprId,
                     x: ExprId,
                     body: &dyn Fn(&mut IntDev<'_>, [ExprId; 5]) -> ExprId|
     -> ExprId {
        let [t1, t2, t3, t4] = hyps(d, c, x);
        let t5 = entry_nonzero(d, p, m, r, j);
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
        let c_fv = d.fresh_fvar();
        let c = d.kernel().fvar(c_fv);
        let zero_n = d.zero();
        let body = bind_hyps(d, c, zero_n, &|d, hs| {
            let lt_of_lt_of_le = d.prelude().lt_of_lt_of_le;
            let lt_irrefl = d.prelude().lt_irrefl;
            let self_lt = d.lemma(lt_of_lt_of_le, &[j, c, j, hs[2], hs[0]]);
            let contradiction = d.lemma(lt_irrefl, &[j, self_lt]);
            let scanned = d.const_app(p.leading_index_aux, &[m, r, cols, zero_n, c]);
            let goal = d.eq(scanned, j);
            absurd(d, goal, contradiction)
        });
        d.lam_fv(c_fv, nat, body)
    };

    let step = |d: &mut IntDev<'_>, n: ExprId, ih: ExprId| -> ExprId {
        let c_fv = d.fresh_fvar();
        let c = d.kernel().fvar(c_fv);
        let sn = d.succ(n);

        let body = bind_hyps(d, c, sn, &|d, hs| {
            let entry = d.apply(m, &[r, c]);
            let is_zero = ris_zero_b(d, p, entry);
            let sc = d.succ(c);
            let recursed = d.const_app(p.leading_index_aux, &[m, r, cols, n, sc]);
            let inner_col = bool_select_at(d, nat, is_zero, recursed, c);
            let oor = NatOps::ble(d, cols, c);

            let outer_shape = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
                let chosen = bool_select_at(d, nat, x, cols, inner_col);
                d.eq(chosen, j)
            };
            let goal = outer_shape(d, oor);

            let true_ = d.bool_true();
            let false_ = d.bool_false();
            let h_true_ty = d.bool_eq(oor, true_);
            let h_false_ty = d.bool_eq(oor, false_);

            // `Nat.ble cols c = true` says the scan ran off the end, but
            // `Le c j` and `Lt j cols` put `c` strictly inside.
            let left_minor = {
                let ht_fv = d.fresh_fvar();
                let ht = d.kernel().fvar(ht_fv);
                let le_of_ble_eq_true = d.prelude().le_of_ble_eq_true;
                let lt_of_le_of_lt = d.prelude().lt_of_le_of_lt;
                let lt_of_lt_of_le = d.prelude().lt_of_lt_of_le;
                let lt_irrefl = d.prelude().lt_irrefl;
                let cols_le_c = d.lemma(le_of_ble_eq_true, &[cols, c, ht]);
                let c_lt_cols = d.lemma(lt_of_le_of_lt, &[c, j, cols, hs[0], hs[1]]);
                let self_lt = d.lemma(lt_of_lt_of_le, &[c, cols, c, c_lt_cols, cols_le_c]);
                let contradiction = d.lemma(lt_irrefl, &[c, self_lt]);
                let target = outer_shape(d, true_);
                let refl_case = absurd(d, target, contradiction);
                let motive_x = d.bool_eq_motive(true_, &outer_shape);
                let ht_sym = d.bool_symm(oor, true_, ht);
                let inner = d.bool_transport(true_, motive_x, refl_case, oor, ht_sym);
                d.lam_fv(ht_fv, h_true_ty, inner)
            };

            let right_minor = {
                let hf_fv = d.fresh_fvar();
                let hf = d.kernel().fvar(hf_fv);

                let inner_shape = |d: &mut IntDev<'_>, y: ExprId| -> ExprId {
                    let chosen = bool_select_at(d, nat, y, recursed, c);
                    d.eq(chosen, j)
                };
                let inner_goal = inner_shape(d, is_zero);
                let zero_true_ty = d.bool_eq(is_zero, true_);
                let zero_false_ty = d.bool_eq(is_zero, false_);

                // `M r c = 0`: `c` cannot be `j` (the entry there is nonzero),
                // so the scan moved on and the induction hypothesis answers.
                let zero_left = {
                    let hz_fv = d.fresh_fvar();
                    let hz = d.kernel().fvar(hz_fv);
                    let refl_case = {
                        let lt_or_eq_of_le = d.prelude().lt_or_eq_of_le;
                        let split = d.lemma(lt_or_eq_of_le, &[c, j, hs[0]]);
                        let lt_ty = NatOps::lt(d, c, j);
                        let eq_ty = d.eq(c, j);
                        let target = inner_shape(d, true_);

                        let below = {
                            let hlt_fv = d.fresh_fvar();
                            let hlt = d.kernel().fvar(hlt_fv);
                            let a3 = {
                                let succ_add = d.prelude().succ_add;
                                let shifted = d.lemma(succ_add, &[c, n]);
                                let left = NatOps::add(d, sc, n);
                                let sum = NatOps::add(d, c, n);
                                let right = d.succ(sum);
                                let back = NatOps::symm(d, left, right, shifted);
                                nat_rewrite_prop(d, right, left, back, hs[2], &|d, t| {
                                    NatOps::lt(d, j, t)
                                })
                            };
                            let a4 = zero_between_shift(d, c, j, hs[3]);
                            let applied = d.apply(ih, &[sc, hlt, hs[1], a3, a4, hs[4]]);
                            d.lam_fv(hlt_fv, lt_ty, applied)
                        };
                        let here = {
                            let heq_fv = d.fresh_fvar();
                            let heq = d.kernel().fvar(heq_fv);
                            let at_c = d.lemma(p.eq_zero_of_is_zero_b, &[entry, hz]);
                            let moved = nat_rewrite_prop(d, c, j, heq, at_c, &|d, t| {
                                entry_zero(d, p, m, r, t)
                            });
                            let contradiction = d.apply(hs[4], &[moved]);
                            let inner = absurd(d, target, contradiction);
                            d.lam_fv(heq_fv, eq_ty, inner)
                        };

                        or_cases(d, lt_ty, eq_ty, target, below, here, split)
                    };
                    let motive_y = d.bool_eq_motive(true_, &inner_shape);
                    let hz_sym = d.bool_symm(is_zero, true_, hz);
                    let inner = d.bool_transport(true_, motive_y, refl_case, is_zero, hz_sym);
                    d.lam_fv(hz_fv, zero_true_ty, inner)
                };

                // `M r c ≠ 0`: the scan stops at `c`, and `c` must BE `j` —
                // anything strictly below `j` is zero by hypothesis.
                let zero_right = {
                    let hz_fv = d.fresh_fvar();
                    let hz = d.kernel().fvar(hz_fv);
                    let refl_case = {
                        let lt_or_eq_of_le = d.prelude().lt_or_eq_of_le;
                        let split = d.lemma(lt_or_eq_of_le, &[c, j, hs[0]]);
                        let lt_ty = NatOps::lt(d, c, j);
                        let eq_ty = d.eq(c, j);
                        let target = inner_shape(d, false_);

                        let below = {
                            let hlt_fv = d.fresh_fvar();
                            let hlt = d.kernel().fvar(hlt_fv);
                            let le_refl = d.prelude().le_refl_thm;
                            let here_le = d.lemma(le_refl, &[c]);
                            let is_zero_here = d.apply(hs[3], &[c, here_le, hlt]);
                            let ne = d.lemma(p.ne_zero_of_is_zero_b_false, &[entry, hz]);
                            let contradiction = d.apply(ne, &[is_zero_here]);
                            let inner = absurd(d, target, contradiction);
                            d.lam_fv(hlt_fv, lt_ty, inner)
                        };
                        let here = {
                            let heq_fv = d.fresh_fvar();
                            let heq = d.kernel().fvar(heq_fv);
                            d.lam_fv(heq_fv, eq_ty, heq)
                        };

                        or_cases(d, lt_ty, eq_ty, target, below, here, split)
                    };
                    let motive_y = d.bool_eq_motive(false_, &inner_shape);
                    let hz_sym = d.bool_symm(is_zero, false_, hz);
                    let inner = d.bool_transport(false_, motive_y, refl_case, is_zero, hz_sym);
                    d.lam_fv(hz_fv, zero_false_ty, inner)
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
                let hf_sym = d.bool_symm(oor, false_, hf);
                let inner = d.bool_transport(false_, motive_x, inner_proof, oor, hf_sym);
                d.lam_fv(hf_fv, h_false_ty, inner)
            };

            let split = bool_cases(d, oor);
            or_cases(
                d,
                h_true_ty,
                h_false_ty,
                goal,
                left_minor,
                right_minor,
                split,
            )
        });
        d.lam_fv(c_fv, nat, body)
    };

    let proof = d.induct(&motive, &base, &step, fuel);

    let ty = {
        let over_fuel = d.pi_fv(fuel_fv, nat, stmt);
        let over_j = d.pi_fv(j_fv, nat, over_fuel);
        let over_cols = d.pi_fv(cols_fv, nat, over_j);
        let over_r = d.pi_fv(r_fv, nat, over_cols);
        d.pi_fv(m_fv, mty, over_r)
    };
    let value = {
        let over_fuel = d.lam_fv(fuel_fv, nat, proof);
        let over_j = d.lam_fv(j_fv, nat, over_fuel);
        let over_cols = d.lam_fv(cols_fv, nat, over_j);
        let over_r = d.lam_fv(r_fv, nat, over_cols);
        d.lam_fv(m_fv, mty, over_r)
    };
    d.declare_theorem(p.leading_index_aux_eq_of_first_nonzero, ty, value)
}

/// Admit `Rat.leadingIndex_eq_of_first_nonzero : ∀ M r cols j, Lt j cols →
/// (∀ k, Lt k j → Eq Rat (M r k) Rat.zero) → Not (Eq Rat (M r j) Rat.zero) →
/// Eq Nat (leadingIndex M r cols) j`.
///
/// [`declare_leading_index_aux_eq_of_first_nonzero`] at the fuel and start
/// index `leadingIndex` picks. `Nat.zero_add` is a THEOREM here (`Nat.add`
/// recurses on its right argument), so the fuel bound `Lt j (0 + cols)` is one
/// transport rather than a reduction.
fn declare_leading_index_eq_of_first_nonzero(
    d: &mut IntDev<'_>,
    p: RatPrelude,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let mty = mat_ty(d);

    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let r_fv = d.fresh_fvar();
    let r = d.kernel().fvar(r_fv);
    let cols_fv = d.fresh_fvar();
    let cols = d.kernel().fvar(cols_fv);
    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);

    let zero_n = d.zero();
    let t1 = NatOps::lt(d, j, cols);
    let t2 = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let upper = NatOps::lt(d, k, j);
        let concl = entry_zero(d, p, m, r, k);
        let body = d.arrow(upper, concl);
        d.pi_fv(k_fv, nat, body)
    };
    let t3 = entry_nonzero(d, p, m, r, j);
    let scanned = d.const_app(p.leading_index, &[m, r, cols]);
    let concl = d.eq(scanned, j);

    let h1_fv = d.fresh_fvar();
    let h1 = d.kernel().fvar(h1_fv);
    let h2_fv = d.fresh_fvar();
    let h2 = d.kernel().fvar(h2_fv);
    let h3_fv = d.fresh_fvar();
    let h3 = d.kernel().fvar(h3_fv);

    let zero_le = d.prelude().zero_le;
    let start_le = d.lemma(zero_le, &[j]);
    let bound = {
        let zero_add = d.prelude().zero_add;
        let shifted = d.lemma(zero_add, &[cols]);
        let sum = NatOps::add(d, zero_n, cols);
        let back = NatOps::symm(d, sum, cols, shifted);
        nat_rewrite_prop(d, cols, sum, back, h1, &|d, t| NatOps::lt(d, j, t))
    };
    // `∀ k, Le 0 k → Lt k j → …` from `∀ k, Lt k j → …`: the lower bound is
    // free at `0` and simply discarded.
    let ranged = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let lower = NatOps::le(d, zero_n, k);
        let upper = NatOps::lt(d, k, j);
        let hk1_fv = d.fresh_fvar();
        let hk2_fv = d.fresh_fvar();
        let hk2 = d.kernel().fvar(hk2_fv);
        let applied = d.apply(h2, &[k, hk2]);
        let with_hk2 = d.lam_fv(hk2_fv, upper, applied);
        let with_hk1 = d.lam_fv(hk1_fv, lower, with_hk2);
        d.lam_fv(k_fv, nat, with_hk1)
    };
    let aux = d.lemma(
        p.leading_index_aux_eq_of_first_nonzero,
        &[m, r, cols, j, cols, zero_n],
    );
    let body = d.apply(aux, &[start_le, h1, bound, ranged, h3]);
    let proof = {
        let l3 = d.lam_fv(h3_fv, t3, body);
        let l2 = d.lam_fv(h2_fv, t2, l3);
        d.lam_fv(h1_fv, t1, l2)
    };

    let ty = {
        let f3 = d.pi_fv(h3_fv, t3, concl);
        let f2 = d.pi_fv(h2_fv, t2, f3);
        let f1 = d.pi_fv(h1_fv, t1, f2);
        let over_j = d.pi_fv(j_fv, nat, f1);
        let over_cols = d.pi_fv(cols_fv, nat, over_j);
        let over_r = d.pi_fv(r_fv, nat, over_cols);
        d.pi_fv(m_fv, mty, over_r)
    };
    let value = {
        let over_j = d.lam_fv(j_fv, nat, proof);
        let over_cols = d.lam_fv(cols_fv, nat, over_j);
        let over_r = d.lam_fv(r_fv, nat, over_cols);
        d.lam_fv(m_fv, mty, over_r)
    };
    d.declare_theorem(p.leading_index_eq_of_first_nonzero, ty, value)
}

/// Admit `Rat.leadingIndexAux_eq_cols_of_zero : ∀ M r cols c fuel,
/// Le cols (Nat.add c fuel) →
/// (∀ k, Le c k → Lt k cols → Eq Rat (M r k) Rat.zero) →
/// Eq Nat (leadingIndexAux M r cols fuel c) cols`.
///
/// Both exhaustion leaves close by `Eq.refl`: the scan's give-up answer is
/// `cols`, which is the conclusion. The `isZeroB = false` leaf is the one
/// refuted, and it is where `Nat.lt_of_ble_eq_false` is spent — the scan's
/// in-range branch is the only place `Lt c cols` is available, and the
/// zero-range hypothesis will not answer without it.
fn declare_leading_index_aux_eq_cols_of_zero(
    d: &mut IntDev<'_>,
    p: RatPrelude,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let mty = mat_ty(d);

    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let r_fv = d.fresh_fvar();
    let r = d.kernel().fvar(r_fv);
    let cols_fv = d.fresh_fvar();
    let cols = d.kernel().fvar(cols_fv);
    let fuel_fv = d.fresh_fvar();
    let fuel = d.kernel().fvar(fuel_fv);

    let hyps = |d: &mut IntDev<'_>, c: ExprId, x: ExprId| -> [ExprId; 2] {
        let bound = NatOps::add(d, c, x);
        let h1 = NatOps::le(d, cols, bound);
        let h2 = zero_between(d, p, m, r, c, cols);
        [h1, h2]
    };

    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let c_fv = d.fresh_fvar();
        let c = d.kernel().fvar(c_fv);
        let scanned = d.const_app(p.leading_index_aux, &[m, r, cols, x, c]);
        let concl = d.eq(scanned, cols);
        let [h1, h2] = hyps(d, c, x);
        let after2 = d.arrow(h2, concl);
        let body = d.arrow(h1, after2);
        d.pi_fv(c_fv, nat, body)
    };
    let stmt = motive(d, fuel);

    let bind_hyps = |d: &mut IntDev<'_>,
                     c: ExprId,
                     x: ExprId,
                     body: &dyn Fn(&mut IntDev<'_>, [ExprId; 2]) -> ExprId|
     -> ExprId {
        let [t1, t2] = hyps(d, c, x);
        let f1 = d.fresh_fvar();
        let f2 = d.fresh_fvar();
        let v1 = d.kernel().fvar(f1);
        let v2 = d.kernel().fvar(f2);
        let inner = body(d, [v1, v2]);
        let l2 = d.lam_fv(f2, t2, inner);
        d.lam_fv(f1, t1, l2)
    };

    let base = |d: &mut IntDev<'_>| -> ExprId {
        let c_fv = d.fresh_fvar();
        let c = d.kernel().fvar(c_fv);
        let zero_n = d.zero();
        let body = bind_hyps(d, c, zero_n, &|d, _hs| {
            // At no fuel the scan answers `cols`, which is the conclusion.
            d.refl(cols)
        });
        d.lam_fv(c_fv, nat, body)
    };

    let step = |d: &mut IntDev<'_>, n: ExprId, ih: ExprId| -> ExprId {
        let c_fv = d.fresh_fvar();
        let c = d.kernel().fvar(c_fv);
        let sn = d.succ(n);

        let body = bind_hyps(d, c, sn, &|d, hs| {
            let entry = d.apply(m, &[r, c]);
            let is_zero = ris_zero_b(d, p, entry);
            let sc = d.succ(c);
            let recursed = d.const_app(p.leading_index_aux, &[m, r, cols, n, sc]);
            let inner_col = bool_select_at(d, nat, is_zero, recursed, c);
            let oor = NatOps::ble(d, cols, c);

            let outer_shape = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
                let chosen = bool_select_at(d, nat, x, cols, inner_col);
                d.eq(chosen, cols)
            };
            let goal = outer_shape(d, oor);

            let true_ = d.bool_true();
            let false_ = d.bool_false();
            let h_true_ty = d.bool_eq(oor, true_);
            let h_false_ty = d.bool_eq(oor, false_);

            // The scan ran off the end and answered `cols`. Free.
            let left_minor = {
                let ht_fv = d.fresh_fvar();
                let ht = d.kernel().fvar(ht_fv);
                let refl_case = d.refl(cols);
                let motive_x = d.bool_eq_motive(true_, &outer_shape);
                let ht_sym = d.bool_symm(oor, true_, ht);
                let inner = d.bool_transport(true_, motive_x, refl_case, oor, ht_sym);
                d.lam_fv(ht_fv, h_true_ty, inner)
            };

            let right_minor = {
                let hf_fv = d.fresh_fvar();
                let hf = d.kernel().fvar(hf_fv);

                let inner_shape = |d: &mut IntDev<'_>, y: ExprId| -> ExprId {
                    let chosen = bool_select_at(d, nat, y, recursed, c);
                    d.eq(chosen, cols)
                };
                let inner_goal = inner_shape(d, is_zero);
                let zero_true_ty = d.bool_eq(is_zero, true_);
                let zero_false_ty = d.bool_eq(is_zero, false_);

                // THE strict bridge: the `false` branch is the only place the
                // column index is known to be inside `cols`.
                let lt_of_ble_eq_false = d.prelude().lt_of_ble_eq_false;
                let c_lt_cols = d.lemma(lt_of_ble_eq_false, &[cols, c, hf]);

                let zero_left = {
                    let hz_fv = d.fresh_fvar();
                    let hz = d.kernel().fvar(hz_fv);
                    let refl_case = {
                        let a1 = {
                            let succ_add = d.prelude().succ_add;
                            let shifted = d.lemma(succ_add, &[c, n]);
                            let left = NatOps::add(d, sc, n);
                            let sum = NatOps::add(d, c, n);
                            let right = d.succ(sum);
                            let back = NatOps::symm(d, left, right, shifted);
                            nat_rewrite_prop(d, right, left, back, hs[0], &|d, t| {
                                NatOps::le(d, cols, t)
                            })
                        };
                        let a2 = zero_between_shift(d, c, cols, hs[1]);
                        d.apply(ih, &[sc, a1, a2])
                    };
                    let motive_y = d.bool_eq_motive(true_, &inner_shape);
                    let hz_sym = d.bool_symm(is_zero, true_, hz);
                    let inner = d.bool_transport(true_, motive_y, refl_case, is_zero, hz_sym);
                    d.lam_fv(hz_fv, zero_true_ty, inner)
                };

                // A nonzero entry strictly inside the range contradicts the
                // hypothesis outright.
                let zero_right = {
                    let hz_fv = d.fresh_fvar();
                    let hz = d.kernel().fvar(hz_fv);
                    let refl_case = {
                        let le_refl = d.prelude().le_refl_thm;
                        let here_le = d.lemma(le_refl, &[c]);
                        let is_zero_here = d.apply(hs[1], &[c, here_le, c_lt_cols]);
                        let ne = d.lemma(p.ne_zero_of_is_zero_b_false, &[entry, hz]);
                        let contradiction = d.apply(ne, &[is_zero_here]);
                        let target = inner_shape(d, false_);
                        absurd(d, target, contradiction)
                    };
                    let motive_y = d.bool_eq_motive(false_, &inner_shape);
                    let hz_sym = d.bool_symm(is_zero, false_, hz);
                    let inner = d.bool_transport(false_, motive_y, refl_case, is_zero, hz_sym);
                    d.lam_fv(hz_fv, zero_false_ty, inner)
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
                let hf_sym = d.bool_symm(oor, false_, hf);
                let inner = d.bool_transport(false_, motive_x, inner_proof, oor, hf_sym);
                d.lam_fv(hf_fv, h_false_ty, inner)
            };

            let split = bool_cases(d, oor);
            or_cases(
                d,
                h_true_ty,
                h_false_ty,
                goal,
                left_minor,
                right_minor,
                split,
            )
        });
        d.lam_fv(c_fv, nat, body)
    };

    let proof = d.induct(&motive, &base, &step, fuel);

    let ty = {
        let over_fuel = d.pi_fv(fuel_fv, nat, stmt);
        let over_cols = d.pi_fv(cols_fv, nat, over_fuel);
        let over_r = d.pi_fv(r_fv, nat, over_cols);
        d.pi_fv(m_fv, mty, over_r)
    };
    let value = {
        let over_fuel = d.lam_fv(fuel_fv, nat, proof);
        let over_cols = d.lam_fv(cols_fv, nat, over_fuel);
        let over_r = d.lam_fv(r_fv, nat, over_cols);
        d.lam_fv(m_fv, mty, over_r)
    };
    d.declare_theorem(p.leading_index_aux_eq_cols_of_zero, ty, value)
}

/// Admit `Rat.leadingIndex_eq_cols_of_zero_row : ∀ M r cols,
/// (∀ k, Lt k cols → Eq Rat (M r k) Rat.zero) →
/// Eq Nat (leadingIndex M r cols) cols`.
///
/// *A zero row's leading index is `cols`* — ADR-1554 §3's design decision,
/// finally as a theorem rather than a property of the definition. It is what
/// `Rat.echelonStepOk` reads as "this row is zero", and what `Rat.rank`
/// declines to count.
fn declare_leading_index_eq_cols_of_zero_row(
    d: &mut IntDev<'_>,
    p: RatPrelude,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let mty = mat_ty(d);

    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let r_fv = d.fresh_fvar();
    let r = d.kernel().fvar(r_fv);
    let cols_fv = d.fresh_fvar();
    let cols = d.kernel().fvar(cols_fv);

    let zero_n = d.zero();
    let t1 = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let upper = NatOps::lt(d, k, cols);
        let concl = entry_zero(d, p, m, r, k);
        let body = d.arrow(upper, concl);
        d.pi_fv(k_fv, nat, body)
    };
    let scanned = d.const_app(p.leading_index, &[m, r, cols]);
    let concl = d.eq(scanned, cols);

    let h1_fv = d.fresh_fvar();
    let h1 = d.kernel().fvar(h1_fv);

    let bound = {
        let le_refl = d.prelude().le_refl_thm;
        let zero_add = d.prelude().zero_add;
        let here = d.lemma(le_refl, &[cols]);
        let shifted = d.lemma(zero_add, &[cols]);
        let sum = NatOps::add(d, zero_n, cols);
        let back = NatOps::symm(d, sum, cols, shifted);
        nat_rewrite_prop(d, cols, sum, back, here, &|d, t| NatOps::le(d, cols, t))
    };
    let ranged = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let lower = NatOps::le(d, zero_n, k);
        let upper = NatOps::lt(d, k, cols);
        let hk1_fv = d.fresh_fvar();
        let hk2_fv = d.fresh_fvar();
        let hk2 = d.kernel().fvar(hk2_fv);
        let applied = d.apply(h1, &[k, hk2]);
        let with_hk2 = d.lam_fv(hk2_fv, upper, applied);
        let with_hk1 = d.lam_fv(hk1_fv, lower, with_hk2);
        d.lam_fv(k_fv, nat, with_hk1)
    };
    let aux = d.lemma(
        p.leading_index_aux_eq_cols_of_zero,
        &[m, r, cols, cols, zero_n],
    );
    let body = d.apply(aux, &[bound, ranged]);
    let proof = d.lam_fv(h1_fv, t1, body);

    let ty = {
        let f1 = d.pi_fv(h1_fv, t1, concl);
        let over_cols = d.pi_fv(cols_fv, nat, f1);
        let over_r = d.pi_fv(r_fv, nat, over_cols);
        d.pi_fv(m_fv, mty, over_r)
    };
    let value = {
        let over_cols = d.lam_fv(cols_fv, nat, proof);
        let over_r = d.lam_fv(r_fv, nat, over_cols);
        d.lam_fv(m_fv, mty, over_r)
    };
    d.declare_theorem(p.leading_index_eq_cols_of_zero_row, ty, value)
}
