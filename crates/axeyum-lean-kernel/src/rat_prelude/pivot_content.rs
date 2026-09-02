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
use super::ops::{nat_rewrite_prop, rat_ty, req, rzero};
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
    declare_pivot_search_aux_column_zero(d, p)?;
    declare_pivot_search_column_zero(d, p)?;
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

/// `Eq Rat (M q c) Rat.zero` — the conclusion of the exhaustion disjunct.
fn entry_eq_zero(d: &mut IntDev<'_>, p: RatPrelude, m: ExprId, r: ExprId, c: ExprId) -> ExprId {
    let entry = d.apply(m, &[r, c]);
    let zero_r = rzero(d, p);
    req(d, entry, zero_r)
}

/// Admit `Rat.pivotSearchAux_column_zero : ∀ M c rows q fuel r, Le r q →
/// Lt q rows → Lt q (Nat.add r fuel) → Eq Nat (pivotSearchAux M c rows fuel r)
/// rows → Eq Rat (M q c) Rat.zero`.
///
/// ADR-1554's obligation 2, FIRST disjunct: *the answer is `rows`, and then
/// column `c` is zero at every row the scan passed.* ADR-1562 recorded it open
/// and said why — it is a statement about every index the scan VISITED rather
/// than about the one it returned, so it needs the accumulated range in the
/// motive, which is `Le r q` plus the fuel bound.
///
/// **The fuel bound is not removable.** A scan that runs out of fuel answers
/// `rows`, exactly as one that reached the bound does; the two are
/// indistinguishable in the answer, so without `Lt q (r + fuel)` the statement
/// is false at `fuel = 0`. The wrapper discharges it from `Lt q rows` because
/// `pivotSearch` hands the scan `rows` units.
///
/// Three of the four leaves are refutations and only one does work. The
/// `Nat.ble rows r = true` branch is refuted from `Le r q` and `Lt q rows`
/// (the scan cannot have run past the bound while `q` is still inside it), and
/// the `isZeroB = false` branch is refuted from its own hypothesis: there the
/// answer is `r`, so `Eq Nat r rows` transports `Lt r rows` into `Lt rows
/// rows`. Only `isZeroB = true` splits further, into `r = q` (read the zero
/// off `Rat.eq_zero_of_isZeroB`) and `Lt r q` (recurse).
fn declare_pivot_search_aux_column_zero(
    d: &mut IntDev<'_>,
    p: RatPrelude,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let mty = mat_ty(d);

    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let rows_fv = d.fresh_fvar();
    let rows = d.kernel().fvar(rows_fv);
    let q_fv = d.fresh_fvar();
    let q = d.kernel().fvar(q_fv);
    let fuel_fv = d.fresh_fvar();
    let fuel = d.kernel().fvar(fuel_fv);

    // The three hypotheses that do NOT mention the tested `Bool`, so they are
    // bound outside every split.
    let range_hyps = |d: &mut IntDev<'_>, r: ExprId, x: ExprId| -> [ExprId; 3] {
        let h1 = NatOps::le(d, r, q);
        let h2 = NatOps::lt(d, q, rows);
        let bound = NatOps::add(d, r, x);
        let h3 = NatOps::lt(d, q, bound);
        [h1, h2, h3]
    };

    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        let found = d.const_app(p.pivot_search_aux, &[m, c, rows, x, r]);
        let exhausted = d.eq(found, rows);
        let concl = entry_eq_zero(d, p, m, q, c);
        let tail = d.arrow(exhausted, concl);
        let [h1, h2, h3] = range_hyps(d, r, x);
        let after3 = d.arrow(h3, tail);
        let after2 = d.arrow(h2, after3);
        let body = d.arrow(h1, after2);
        d.pi_fv(r_fv, nat, body)
    };
    let stmt = motive(d, fuel);

    let bind_range = |d: &mut IntDev<'_>,
                      r: ExprId,
                      x: ExprId,
                      body: &dyn Fn(&mut IntDev<'_>, [ExprId; 3]) -> ExprId|
     -> ExprId {
        let [t1, t2, t3] = range_hyps(d, r, x);
        let f1 = d.fresh_fvar();
        let f2 = d.fresh_fvar();
        let f3 = d.fresh_fvar();
        let v1 = d.kernel().fvar(f1);
        let v2 = d.kernel().fvar(f2);
        let v3 = d.kernel().fvar(f3);
        let inner = body(d, [v1, v2, v3]);
        let l3 = d.lam_fv(f3, t3, inner);
        let l2 = d.lam_fv(f2, t2, l3);
        d.lam_fv(f1, t1, l2)
    };

    let base = |d: &mut IntDev<'_>| -> ExprId {
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        let zero_n = d.zero();
        let body = bind_range(d, r, zero_n, &|d, hs| {
            // `Lt q (r + 0)` is `Lt q r`; with `Le r q` that is `Lt q q`.
            let lt_of_lt_of_le = d.prelude().lt_of_lt_of_le;
            let lt_irrefl = d.prelude().lt_irrefl;
            let self_lt = d.lemma(lt_of_lt_of_le, &[q, r, q, hs[2], hs[0]]);
            let contradiction = d.lemma(lt_irrefl, &[q, self_lt]);
            let found = d.const_app(p.pivot_search_aux, &[m, c, rows, zero_n, r]);
            let exhausted = d.eq(found, rows);
            let concl = entry_eq_zero(d, p, m, q, c);
            let goal = d.arrow(exhausted, concl);
            absurd(d, goal, contradiction)
        });
        d.lam_fv(r_fv, nat, body)
    };

    let step = |d: &mut IntDev<'_>, n: ExprId, ih: ExprId| -> ExprId {
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        let sn = d.succ(n);

        let body = bind_range(d, r, sn, &|d, hs| {
            let entry = d.apply(m, &[r, c]);
            let is_zero = ris_zero_b(d, p, entry);
            let sr = d.succ(r);
            let recursed = d.const_app(p.pivot_search_aux, &[m, c, rows, n, sr]);
            let inner_row = bool_select_at(d, nat, is_zero, recursed, r);
            let oor = NatOps::ble(d, rows, r);
            let concl = entry_eq_zero(d, p, m, q, c);

            // `r` is strictly inside the row count, from the accumulated range.
            let r_lt_rows = {
                let lt_of_le_of_lt = d.prelude().lt_of_le_of_lt;
                d.lemma(lt_of_le_of_lt, &[r, q, rows, hs[0], hs[1]])
            };

            let outer_shape = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
                let chosen = bool_select_at(d, nat, x, rows, inner_row);
                let exhausted = d.eq(chosen, rows);
                d.arrow(exhausted, concl)
            };
            let goal = outer_shape(d, oor);

            let true_ = d.bool_true();
            let false_ = d.bool_false();
            let h_true_ty = d.bool_eq(oor, true_);
            let h_false_ty = d.bool_eq(oor, false_);

            let left_minor = {
                let ht_fv = d.fresh_fvar();
                let ht = d.kernel().fvar(ht_fv);
                let le_of_ble_eq_true = d.prelude().le_of_ble_eq_true;
                let lt_of_lt_of_le = d.prelude().lt_of_lt_of_le;
                let lt_irrefl = d.prelude().lt_irrefl;
                let rows_le_r = d.lemma(le_of_ble_eq_true, &[rows, r, ht]);
                let self_lt = d.lemma(lt_of_lt_of_le, &[r, rows, r, r_lt_rows, rows_le_r]);
                let contradiction = d.lemma(lt_irrefl, &[r, self_lt]);
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
                    let chosen = bool_select_at(d, nat, y, recursed, r);
                    let exhausted = d.eq(chosen, rows);
                    d.arrow(exhausted, concl)
                };
                let inner_goal = inner_shape(d, is_zero);
                let zero_true_ty = d.bool_eq(is_zero, true_);
                let zero_false_ty = d.bool_eq(is_zero, false_);

                // `M r c = 0`: either `r` IS the row asked about, or the scan
                // moved on and the induction hypothesis answers.
                let zero_left = {
                    let hz_fv = d.fresh_fvar();
                    let hz = d.kernel().fvar(hz_fv);
                    let refl_case = {
                        let he_fv = d.fresh_fvar();
                        let he = d.kernel().fvar(he_fv);
                        let assumed = d.eq(recursed, rows);

                        let lt_or_eq_of_le = d.prelude().lt_or_eq_of_le;
                        let split = d.lemma(lt_or_eq_of_le, &[r, q, hs[0]]);
                        let lt_ty = NatOps::lt(d, r, q);
                        let eq_ty = d.eq(r, q);

                        let below = {
                            let hlt_fv = d.fresh_fvar();
                            let hlt = d.kernel().fvar(hlt_fv);
                            let a3 = {
                                let succ_add = d.prelude().succ_add;
                                let shifted = d.lemma(succ_add, &[r, n]);
                                let left = NatOps::add(d, sr, n);
                                let sum = NatOps::add(d, r, n);
                                let right = d.succ(sum);
                                let back = NatOps::symm(d, left, right, shifted);
                                nat_rewrite_prop(d, right, left, back, hs[2], &|d, t| {
                                    NatOps::lt(d, q, t)
                                })
                            };
                            let applied = d.apply(ih, &[sr, hlt, hs[1], a3, he]);
                            d.lam_fv(hlt_fv, lt_ty, applied)
                        };
                        let here = {
                            let heq_fv = d.fresh_fvar();
                            let heq = d.kernel().fvar(heq_fv);
                            let at_r = d.lemma(p.eq_zero_of_is_zero_b, &[entry, hz]);
                            let moved = nat_rewrite_prop(d, r, q, heq, at_r, &|d, t| {
                                entry_eq_zero(d, p, m, t, c)
                            });
                            d.lam_fv(heq_fv, eq_ty, moved)
                        };

                        let chosen = or_cases(d, lt_ty, eq_ty, concl, below, here, split);
                        d.lam_fv(he_fv, assumed, chosen)
                    };
                    let motive_y = d.bool_eq_motive(true_, &inner_shape);
                    let hz_sym = d.bool_symm(is_zero, true_, hz);
                    let inner = d.bool_transport(true_, motive_y, refl_case, is_zero, hz_sym);
                    d.lam_fv(hz_fv, zero_true_ty, inner)
                };

                // `M r c ≠ 0`: the scan answers `r`, so the exhaustion
                // hypothesis says `r = rows`, which `Lt r rows` refutes.
                let zero_right = {
                    let hz_fv = d.fresh_fvar();
                    let hz = d.kernel().fvar(hz_fv);
                    let refl_case = {
                        let he_fv = d.fresh_fvar();
                        let he = d.kernel().fvar(he_fv);
                        let assumed = d.eq(r, rows);
                        let moved = nat_rewrite_prop(d, r, rows, he, r_lt_rows, &|d, t| {
                            NatOps::lt(d, t, rows)
                        });
                        let lt_irrefl = d.prelude().lt_irrefl;
                        let contradiction = d.lemma(lt_irrefl, &[rows, moved]);
                        let inner = absurd(d, concl, contradiction);
                        d.lam_fv(he_fv, assumed, inner)
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
        d.lam_fv(r_fv, nat, body)
    };

    let proof = d.induct(&motive, &base, &step, fuel);

    let ty = {
        let over_fuel = d.pi_fv(fuel_fv, nat, stmt);
        let over_q = d.pi_fv(q_fv, nat, over_fuel);
        let over_rows = d.pi_fv(rows_fv, nat, over_q);
        let over_c = d.pi_fv(c_fv, nat, over_rows);
        d.pi_fv(m_fv, mty, over_c)
    };
    let value = {
        let over_fuel = d.lam_fv(fuel_fv, nat, proof);
        let over_q = d.lam_fv(q_fv, nat, over_fuel);
        let over_rows = d.lam_fv(rows_fv, nat, over_q);
        let over_c = d.lam_fv(c_fv, nat, over_rows);
        d.lam_fv(m_fv, mty, over_c)
    };
    d.declare_theorem(p.pivot_search_aux_column_zero, ty, value)
}

/// Admit `Rat.pivotSearch_column_zero : ∀ M c start rows q, Le start q →
/// Lt q rows → Eq Nat (pivotSearch M c start rows) rows →
/// Eq Rat (M q c) Rat.zero`.
///
/// Obligation 2 is now complete: range half (`pivot_bound.rs`), value half
/// (above), exhaustion disjunct (here). The fuel bound
/// [`declare_pivot_search_aux_column_zero`] needs is discharged from `Lt q
/// rows` and `Nat.le_add_right`, because `pivotSearch` hands the scan `rows`
/// units of fuel and the scan starts at `start`.
fn declare_pivot_search_column_zero(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
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
    let q_fv = d.fresh_fvar();
    let q = d.kernel().fvar(q_fv);

    let t1 = NatOps::le(d, start, q);
    let t2 = NatOps::lt(d, q, rows);
    let found = d.const_app(p.pivot_search, &[m, c, start, rows]);
    let t3 = d.eq(found, rows);
    let concl = entry_eq_zero(d, p, m, q, c);

    let h1_fv = d.fresh_fvar();
    let h1 = d.kernel().fvar(h1_fv);
    let h2_fv = d.fresh_fvar();
    let h2 = d.kernel().fvar(h2_fv);
    let h3_fv = d.fresh_fvar();
    let h3 = d.kernel().fvar(h3_fv);

    let bound = {
        let le_add_right = d.prelude().le_add_right;
        let add_comm = d.prelude().add_comm;
        let lt_of_lt_of_le = d.prelude().lt_of_lt_of_le;
        let grown = d.lemma(le_add_right, &[rows, start]);
        let right_sum = NatOps::add(d, rows, start);
        let left_sum = NatOps::add(d, start, rows);
        let flip = d.lemma(add_comm, &[rows, start]);
        let moved = nat_rewrite_prop(d, right_sum, left_sum, flip, grown, &|d, t| {
            NatOps::le(d, rows, t)
        });
        d.lemma(lt_of_lt_of_le, &[q, rows, left_sum, h2, moved])
    };
    let aux = d.lemma(
        p.pivot_search_aux_column_zero,
        &[m, c, rows, q, rows, start],
    );
    let body = d.apply(aux, &[h1, h2, bound, h3]);
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
        let over_rows = d.pi_fv(rows_fv, nat, over_q);
        let over_start = d.pi_fv(start_fv, nat, over_rows);
        let over_c = d.pi_fv(c_fv, nat, over_start);
        d.pi_fv(m_fv, mty, over_c)
    };
    let value = {
        let over_q = d.lam_fv(q_fv, nat, proof);
        let over_rows = d.lam_fv(rows_fv, nat, over_q);
        let over_start = d.lam_fv(start_fv, nat, over_rows);
        let over_c = d.lam_fv(c_fv, nat, over_start);
        d.lam_fv(m_fv, mty, over_c)
    };
    d.declare_theorem(p.pivot_search_column_zero, ty, value)
}
