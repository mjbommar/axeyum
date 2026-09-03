//! From row-echelon form to the **pivot section**, and the ADR-1562 bridge
//! unconditional.
//!
//! ADR-1562 §2 measured that the whole of ADR-1554's obligation 4, *as the
//! `rank = rankCols` bridge consumes it*, is one equation:
//!
//! ```text
//! ∀ r, Lt r rows → nonzeroRowB E cols r = true →
//!   pivotRowOfCol E rows cols (pivotColOfRow E cols r) = r
//! ```
//!
//! — *the first row whose leading index is row `r`'s is `r` itself* — and that
//! this is strictly weaker than `isEchelon E rows cols = true`, which also
//! asserts that zero rows sit last. ADR-1574 closed obligation 4. This module
//! is the implication between them, and then the three `_of_pivotSection`
//! results become unconditional.
//!
//! ## Why it is not immediate
//!
//! `isEchelon` checks ADJACENT pairs only. The section needs row `r`'s leading
//! index to differ from that of EVERY row above it, which is distinctness at a
//! distance. Three things bridge the gap.
//!
//! 1. **`Rat.pairs_of_isEchelon`** — the converse of
//!    `Rat.isEchelon_of_pairs`, reading the pair condition back out of the
//!    computed `Bool`. It needs a fuel bound where the forward direction needed
//!    none: by ADR-1571 §2's rule, `isEchelonAux` answers `true` on exhaustion,
//!    which SATISFIES the forward conclusion and FALSIFIES this one.
//! 2. **`Rat.lt_of_echelonStepOk`** — decoding the test. `echelonStepOk l1 l2
//!    cols = true` together with `Lt l2 cols` forces the FIRST disjunct, because
//!    the second requires `Le cols l2`.
//! 3. **`Rat.leadingIndex_strict_below`** — the chain, by induction on the
//!    LOWER row rather than on the distance between the two. That choice is
//!    what keeps `Nat.add` and `Nat.sub` out of the statement entirely: the
//!    motive is `∀ q, Lt q r → …`, the successor step splits `Le q r'` into
//!    `Lt q r'` (the induction hypothesis) and `Eq q r'` (the adjacent pair),
//!    and no arithmetic on indices is ever formed.
//!
//! ## And the search has to be characterised
//!
//! `pivotRowOfCol` is a computed scan, so knowing that `r` is the unique row
//! with its leading index is not yet knowing what the scan answers.
//! `Rat.pivotRowSearchAux_eq_of_first` is the same shape as
//! `Rat.leadingIndexAux_eq_of_first_nonzero` — *nothing before it matches, it
//! matches, and the fuel reaches it* — and the fuel bound is again forced,
//! because the scan's exhaustion answer is `rows` and `r` is in range.

use super::RatPrelude;
use super::echelon::{bool_select_at, rleading_index};
use super::matrix_det::mat_ty;
use super::ops::nat_rewrite_prop;
use super::rank::rnonzero_row_b;
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
pub(super) fn declare_echelon_section(
    d: &mut IntDev<'_>,
    p: RatPrelude,
) -> Result<(), KernelError> {
    declare_lt_of_echelon_step_ok(d, p)?;
    declare_pairs_of_is_echelon_aux(d, p)?;
    declare_pairs_of_is_echelon(d, p)?;
    declare_leading_index_strict_below(d, p)?;
    declare_pivot_row_search_aux_eq_of_first(d, p)?;
    declare_pivot_row_of_col_eq_of_first(d, p)?;
    declare_pivot_section_of_is_echelon(d, p)?;
    declare_rank_eq_rank_cols(d, p)?;
    declare_rank_le_cols(d, p)?;
    declare_rank_nullity_rows(d, p)?;
    Ok(())
}

/// `Le a b` from `h : Lt a b` — `Nat.le_succ` then `Nat.le_trans`.
fn le_of_lt(d: &mut IntDev<'_>, a: ExprId, b: ExprId, h: ExprId) -> ExprId {
    let sa = d.succ(a);
    let le_succ = d.prelude().le_succ;
    let le_trans = d.prelude().le_trans;
    let up = d.lemma(le_succ, &[a]);
    d.lemma(le_trans, &[a, sa, b, up, h])
}

/// `Not (Eq Nat a b)` from `h : Lt a b`.
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

/// `False` from `h : Eq Bool Bool.false Bool.true`.
fn refute_false_true(d: &mut IntDev<'_>, h: ExprId) -> ExprId {
    let name = d.prelude().logic.bool_false_ne_true;
    d.const_app(name, &[h])
}

/// Admit `Rat.lt_of_echelonStepOk : ∀ l1 l2 cols,
/// Eq Bool (echelonStepOk l1 l2 cols) true → Lt l2 cols → Lt l1 l2`.
///
/// *Decoding the test.* `echelonStepOk` is a disjunction and passing it says
/// only that ONE disjunct held; the second requires `Le cols l2`, so a second
/// row whose leading index is genuinely inside the width forces the FIRST.
///
/// This is the converse direction of `Rat.echelonStepOk_of_lt` and it is not
/// free: both `Bool` splits have to be REFUTED rather than closed, one against
/// `Lt l2 cols` and one against `Bool.false_ne_true`.
fn declare_lt_of_echelon_step_ok(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();

    let l1_fv = d.fresh_fvar();
    let l1 = d.kernel().fvar(l1_fv);
    let l2_fv = d.fresh_fvar();
    let l2 = d.kernel().fvar(l2_fv);
    let cols_fv = d.fresh_fvar();
    let cols = d.kernel().fvar(cols_fv);

    let ok = d.const_app(p.echelon_step_ok, &[l1, l2, cols]);
    let true_ = d.bool_true();
    let false_ = d.bool_false();
    let hok_ty = d.bool_eq(ok, true_);
    let hlt_ty = NatOps::lt(d, l2, cols);
    let concl = NatOps::lt(d, l1, l2);

    let hok_fv = d.fresh_fvar();
    let hok = d.kernel().fvar(hok_fv);
    let hlt_fv = d.fresh_fvar();
    let hlt = d.kernel().fvar(hlt_fv);

    let sl1 = d.succ(l1);
    let strict = NatOps::ble(d, sl1, l2);
    let first_zero = NatOps::ble(d, cols, l1);
    let second_zero = NatOps::ble(d, cols, l2);

    // The whole test as a function of the outer `Bool`, and the second
    // disjunct as a function of the inner one.
    let outer_shape = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let bool_ty = d.bool_ty();
        let f = d.bool_false();
        let both = bool_select_at(d, bool_ty, first_zero, second_zero, f);
        let t = d.bool_true();
        let sel = bool_select_at(d, bool_ty, x, t, both);
        let t2 = d.bool_true();
        d.bool_eq(sel, t2)
    };
    let inner_shape = |d: &mut IntDev<'_>, y: ExprId| -> ExprId {
        let bool_ty = d.bool_ty();
        let f = d.bool_false();
        let sel = bool_select_at(d, bool_ty, y, second_zero, f);
        let t = d.bool_true();
        d.bool_eq(sel, t)
    };

    let strict_true_ty = d.bool_eq(strict, true_);
    let strict_false_ty = d.bool_eq(strict, false_);

    let it_moved = {
        let ht_fv = d.fresh_fvar();
        let ht = d.kernel().fvar(ht_fv);
        let ble_le = d.prelude().le_of_ble_eq_true;
        let body = d.lemma(ble_le, &[sl1, l2, ht]);
        d.lam_fv(ht_fv, strict_true_ty, body)
    };

    let it_did_not = {
        let hf_fv = d.fresh_fvar();
        let hf = d.kernel().fvar(hf_fv);

        // Move the hypothesis to the branch this split fixes.
        let motive_x = d.bool_eq_motive(strict, &outer_shape);
        let disjunct = d.bool_transport(strict, motive_x, hok, false_, hf);

        let first_true_ty = d.bool_eq(first_zero, true_);
        let first_false_ty = d.bool_eq(first_zero, false_);

        let both_zero = {
            let hb_fv = d.fresh_fvar();
            let hb = d.kernel().fvar(hb_fv);
            let motive_y = d.bool_eq_motive(first_zero, &inner_shape);
            let second = d.bool_transport(first_zero, motive_y, disjunct, true_, hb);
            let ble_le = d.prelude().le_of_ble_eq_true;
            let cols_le_l2 = d.lemma(ble_le, &[cols, l2, second]);
            let lt_of_lt_of_le = d.prelude().lt_of_lt_of_le;
            let self_lt = d.lemma(lt_of_lt_of_le, &[l2, cols, l2, hlt, cols_le_l2]);
            let lt_irrefl = d.prelude().lt_irrefl;
            let contradiction = d.lemma(lt_irrefl, &[l2, self_lt]);
            let inner = absurd(d, concl, contradiction);
            d.lam_fv(hb_fv, first_true_ty, inner)
        };
        let neither = {
            let hb_fv = d.fresh_fvar();
            let hb = d.kernel().fvar(hb_fv);
            let motive_y = d.bool_eq_motive(first_zero, &inner_shape);
            let absurd_eq = d.bool_transport(first_zero, motive_y, disjunct, false_, hb);
            let contradiction = refute_false_true(d, absurd_eq);
            let inner = absurd(d, concl, contradiction);
            d.lam_fv(hb_fv, first_false_ty, inner)
        };

        let split = bool_cases(d, first_zero);
        let chosen = or_cases(
            d,
            first_true_ty,
            first_false_ty,
            concl,
            both_zero,
            neither,
            split,
        );
        d.lam_fv(hf_fv, strict_false_ty, chosen)
    };

    let split = bool_cases(d, strict);
    let proof_body = or_cases(
        d,
        strict_true_ty,
        strict_false_ty,
        concl,
        it_moved,
        it_did_not,
        split,
    );

    let ty = {
        let f2 = d.pi_fv(hlt_fv, hlt_ty, concl);
        let f1 = d.pi_fv(hok_fv, hok_ty, f2);
        let over_cols = d.pi_fv(cols_fv, nat, f1);
        let over_l2 = d.pi_fv(l2_fv, nat, over_cols);
        d.pi_fv(l1_fv, nat, over_l2)
    };
    let value = {
        let f2 = d.lam_fv(hlt_fv, hlt_ty, proof_body);
        let f1 = d.lam_fv(hok_fv, hok_ty, f2);
        let over_cols = d.lam_fv(cols_fv, nat, f1);
        let over_l2 = d.lam_fv(l2_fv, nat, over_cols);
        d.lam_fv(l1_fv, nat, over_l2)
    };
    d.declare_theorem(p.lt_of_echelon_step_ok, ty, value)
}

/// `Eq Bool (echelonStepOk (leadingIndex E q cols) (leadingIndex E (succ q)
/// cols) cols) true`.
fn pair_ok_at(d: &mut IntDev<'_>, p: RatPrelude, e: ExprId, cols: ExprId, q: ExprId) -> ExprId {
    let sq = d.succ(q);
    let l1 = rleading_index(d, p, e, q, cols);
    let l2 = rleading_index(d, p, e, sq, cols);
    let ok = d.const_app(p.echelon_step_ok, &[l1, l2, cols]);
    let true_ = d.bool_true();
    d.bool_eq(ok, true_)
}

/// Admit `Rat.pairs_of_isEchelonAux : ∀ E rows cols q fuel r, Le r q →
/// Lt (succ q) rows → Lt q (Nat.add r fuel) →
/// Eq Bool (isEchelonAux E rows cols fuel r) true →
/// Eq Bool (echelonStepOk (leadingIndex E q cols)
///          (leadingIndex E (succ q) cols) cols) true`.
///
/// **The fuel bound is forced, and the contrast with
/// `Rat.isEchelonAux_of_pairs` is exactly ADR-1571 §2's rule.** The forward
/// direction concludes `isEchelonAux … = true`, which the exhaustion answer
/// satisfies, so it needs no bound. This direction concludes something ABOUT a
/// pair the scan may never have reached, and an exhausted scan answers `true`
/// having checked nothing — so `Lt q (Nat.add r fuel)`, *the pair is one of the
/// `fuel` this call will visit*, is what rules that out.
fn declare_pairs_of_is_echelon_aux(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let mty = mat_ty(d);

    let e_fv = d.fresh_fvar();
    let e = d.kernel().fvar(e_fv);
    let rows_fv = d.fresh_fvar();
    let rows = d.kernel().fvar(rows_fv);
    let cols_fv = d.fresh_fvar();
    let cols = d.kernel().fvar(cols_fv);
    let q_fv = d.fresh_fvar();
    let q = d.kernel().fvar(q_fv);

    let sq = d.succ(q);
    let goal = pair_ok_at(d, p, e, cols, q);

    let hyps = |d: &mut IntDev<'_>, r: ExprId, x: ExprId| -> [ExprId; 4] {
        let h1 = NatOps::le(d, r, q);
        let h2 = NatOps::lt(d, sq, rows);
        let sum = NatOps::add(d, r, x);
        let h3 = NatOps::lt(d, q, sum);
        let scanned = d.const_app(p.is_echelon_aux, &[e, rows, cols, x, r]);
        let true_ = d.bool_true();
        let h4 = d.bool_eq(scanned, true_);
        [h1, h2, h3, h4]
    };

    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let nat_i = d.nat_ty();
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        let [t1, t2, t3, t4] = hyps(d, r, x);
        let a4 = d.arrow(t4, goal);
        let a3 = d.arrow(t3, a4);
        let a2 = d.arrow(t2, a3);
        let a1 = d.arrow(t1, a2);
        d.pi_fv(r_fv, nat_i, a1)
    };

    let bind = |d: &mut IntDev<'_>,
                r: ExprId,
                x: ExprId,
                body: &dyn Fn(&mut IntDev<'_>, [ExprId; 4]) -> ExprId|
     -> ExprId {
        let [t1, t2, t3, t4] = hyps(d, r, x);
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

    let zero_n = d.zero();
    let base = |d: &mut IntDev<'_>| -> ExprId {
        let nat_i = d.nat_ty();
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        // `Lt q (Nat.add r 0)` IS `Lt q r`, which `Le r q` refutes.
        let body = bind(d, r, zero_n, &|d, hs| {
            let lt_of_lt_of_le = d.prelude().lt_of_lt_of_le;
            let self_lt = d.lemma(lt_of_lt_of_le, &[q, r, q, hs[2], hs[0]]);
            let lt_irrefl = d.prelude().lt_irrefl;
            let contradiction = d.lemma(lt_irrefl, &[q, self_lt]);
            absurd(d, goal, contradiction)
        });
        d.lam_fv(r_fv, nat_i, body)
    };

    let step = |d: &mut IntDev<'_>, n: ExprId, ih: ExprId| -> ExprId {
        let nat_i = d.nat_ty();
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        let sn = d.succ(n);
        let sr = d.succ(r);

        let body = bind(d, r, sn, &|d, hs| {
            let ok_term = {
                let l1 = rleading_index(d, p, e, r, cols);
                let l2 = rleading_index(d, p, e, sr, cols);
                d.const_app(p.echelon_step_ok, &[l1, l2, cols])
            };
            let rec_next = d.const_app(p.is_echelon_aux, &[e, rows, cols, n, sr]);
            let last_row = NatOps::ble(d, rows, sr);
            let true_ = d.bool_true();
            let false_ = d.bool_false();

            let inner_shape = |d: &mut IntDev<'_>, y: ExprId| -> ExprId {
                let bool_ty = d.bool_ty();
                let f = d.bool_false();
                let sel = bool_select_at(d, bool_ty, y, rec_next, f);
                let t = d.bool_true();
                d.bool_eq(sel, t)
            };
            let outer_shape = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
                let bool_ty = d.bool_ty();
                let inner = {
                    let f = d.bool_false();
                    bool_select_at(d, bool_ty, ok_term, rec_next, f)
                };
                let t = d.bool_true();
                let sel = bool_select_at(d, bool_ty, x, t, inner);
                let t2 = d.bool_true();
                d.bool_eq(sel, t2)
            };

            let last_true_ty = d.bool_eq(last_row, true_);
            let last_false_ty = d.bool_eq(last_row, false_);

            // `Lt (succ r) rows` follows from `Le r q` and `Lt (succ q) rows`,
            // so the "no row below" branch is refuted, not closed.
            let refute_last = {
                let ht_fv = d.fresh_fvar();
                let ht = d.kernel().fvar(ht_fv);
                let le_succ_succ = d.prelude().le_succ_succ;
                let ssr = d.succ(sr);
                let ssq = d.succ(sq);
                let a = d.lemma(le_succ_succ, &[r, q, hs[0]]);
                let b = d.lemma(le_succ_succ, &[sr, sq, a]);
                let le_trans = d.prelude().le_trans;
                let sr_lt_rows = d.lemma(le_trans, &[ssr, ssq, rows, b, hs[1]]);
                let le_of_ble = d.prelude().le_of_ble_eq_true;
                let rows_le_sr = d.lemma(le_of_ble, &[rows, sr, ht]);
                let lt_of_lt_of_le = d.prelude().lt_of_lt_of_le;
                let self_lt = d.lemma(lt_of_lt_of_le, &[sr, rows, sr, sr_lt_rows, rows_le_sr]);
                let lt_irrefl = d.prelude().lt_irrefl;
                let contradiction = d.lemma(lt_irrefl, &[sr, self_lt]);
                let inner = absurd(d, goal, contradiction);
                d.lam_fv(ht_fv, last_true_ty, inner)
            };

            let keep_reading = {
                let hf_fv = d.fresh_fvar();
                let hf = d.kernel().fvar(hf_fv);
                let motive_x = d.bool_eq_motive(last_row, &outer_shape);
                let after_last = d.bool_transport(last_row, motive_x, hs[3], false_, hf);

                let ok_true_ty = d.bool_eq(ok_term, true_);
                let ok_false_ty = d.bool_eq(ok_term, false_);

                let pair_holds = {
                    let hb_fv = d.fresh_fvar();
                    let hb = d.kernel().fvar(hb_fv);
                    let motive_y = d.bool_eq_motive(ok_term, &inner_shape);
                    let tail = d.bool_transport(ok_term, motive_y, after_last, true_, hb);

                    let lt_or_eq_of_le = d.prelude().lt_or_eq_of_le;
                    let split = d.lemma(lt_or_eq_of_le, &[r, q, hs[0]]);
                    let lt_ty = NatOps::lt(d, r, q);
                    let eq_ty = d.eq(r, q);

                    let further_down = {
                        let hx_fv = d.fresh_fvar();
                        let hx = d.kernel().fvar(hx_fv);
                        // `Lt q (Nat.add r (succ n))` is definitionally
                        // `Lt q (succ (Nat.add r n))`; the next level wants
                        // `Lt q (Nat.add (succ r) n)`.
                        let add_r_n = NatOps::add(d, r, n);
                        let s_add = d.succ(add_r_n);
                        let add_sr_n = NatOps::add(d, sr, n);
                        let succ_add = d.prelude().succ_add;
                        let sa = d.lemma(succ_add, &[r, n]);
                        let sa_sym = NatOps::symm(d, add_sr_n, s_add, sa);
                        let next_fuel =
                            nat_rewrite_prop(d, s_add, add_sr_n, sa_sym, hs[2], &|d, t| {
                                NatOps::lt(d, q, t)
                            });
                        let applied = d.apply(ih, &[sr, hx, hs[1], next_fuel, tail]);
                        d.lam_fv(hx_fv, lt_ty, applied)
                    };
                    let this_is_it = {
                        let he_fv = d.fresh_fvar();
                        let he = d.kernel().fvar(he_fv);
                        let moved =
                            nat_rewrite_prop(d, r, q, he, hb, &|d, t| pair_ok_at(d, p, e, cols, t));
                        d.lam_fv(he_fv, eq_ty, moved)
                    };
                    let chosen = or_cases(d, lt_ty, eq_ty, goal, further_down, this_is_it, split);
                    d.lam_fv(hb_fv, ok_true_ty, chosen)
                };
                let pair_fails = {
                    let hb_fv = d.fresh_fvar();
                    let hb = d.kernel().fvar(hb_fv);
                    let motive_y = d.bool_eq_motive(ok_term, &inner_shape);
                    let absurd_eq = d.bool_transport(ok_term, motive_y, after_last, false_, hb);
                    let contradiction = refute_false_true(d, absurd_eq);
                    let inner = absurd(d, goal, contradiction);
                    d.lam_fv(hb_fv, ok_false_ty, inner)
                };

                let split = bool_cases(d, ok_term);
                let chosen = or_cases(
                    d,
                    ok_true_ty,
                    ok_false_ty,
                    goal,
                    pair_holds,
                    pair_fails,
                    split,
                );
                d.lam_fv(hf_fv, last_false_ty, chosen)
            };

            let split = bool_cases(d, last_row);
            or_cases(
                d,
                last_true_ty,
                last_false_ty,
                goal,
                refute_last,
                keep_reading,
                split,
            )
        });
        d.lam_fv(r_fv, nat_i, body)
    };

    let fuel_fv = d.fresh_fvar();
    let fuel = d.kernel().fvar(fuel_fv);
    let proof = d.induct(&motive, &base, &step, fuel);
    let stmt = motive(d, fuel);

    let ty = {
        let over_fuel = d.pi_fv(fuel_fv, nat, stmt);
        let over_q = d.pi_fv(q_fv, nat, over_fuel);
        let over_cols = d.pi_fv(cols_fv, nat, over_q);
        let over_rows = d.pi_fv(rows_fv, nat, over_cols);
        d.pi_fv(e_fv, mty, over_rows)
    };
    let value = {
        let over_fuel = d.lam_fv(fuel_fv, nat, proof);
        let over_q = d.lam_fv(q_fv, nat, over_fuel);
        let over_cols = d.lam_fv(cols_fv, nat, over_q);
        let over_rows = d.lam_fv(rows_fv, nat, over_cols);
        d.lam_fv(e_fv, mty, over_rows)
    };
    d.declare_theorem(p.pairs_of_is_echelon_aux, ty, value)
}

/// Admit `Rat.pairs_of_isEchelon : ∀ E rows cols,
/// Eq Bool (isEchelon E rows cols) true → ∀ q, Lt (succ q) rows →
/// Eq Bool (echelonStepOk (leadingIndex E q cols)
///          (leadingIndex E (succ q) cols) cols) true`.
fn declare_pairs_of_is_echelon(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let mty = mat_ty(d);

    let e_fv = d.fresh_fvar();
    let e = d.kernel().fvar(e_fv);
    let rows_fv = d.fresh_fvar();
    let rows = d.kernel().fvar(rows_fv);
    let cols_fv = d.fresh_fvar();
    let cols = d.kernel().fvar(cols_fv);

    let scanned = d.const_app(p.is_echelon, &[e, rows, cols]);
    let true_ = d.bool_true();
    let hyp_ty = d.bool_eq(scanned, true_);
    let hyp_fv = d.fresh_fvar();
    let hyp = d.kernel().fvar(hyp_fv);

    let q_fv = d.fresh_fvar();
    let q = d.kernel().fvar(q_fv);
    let sq = d.succ(q);
    let bound = NatOps::lt(d, sq, rows);
    let hq_fv = d.fresh_fvar();
    let hq = d.kernel().fvar(hq_fv);
    let goal = pair_ok_at(d, p, e, cols, q);

    let zero_n = d.zero();
    let zero_le = d.prelude().zero_le;
    let zero_le_q = d.lemma(zero_le, &[q]);

    // `Lt q rows` from `Lt (succ q) rows`, then moved to `Nat.add 0 rows`.
    let le_succ = d.prelude().le_succ;
    let le_trans = d.prelude().le_trans;
    let ssq = d.succ(sq);
    let up = d.lemma(le_succ, &[sq]);
    let q_lt_rows = d.lemma(le_trans, &[sq, ssq, rows, up, hq]);
    let sum = NatOps::add(d, zero_n, rows);
    let zero_add = d.prelude().zero_add;
    let za = d.lemma(zero_add, &[rows]);
    let za_sym = NatOps::symm(d, sum, rows, za);
    let in_fuel = nat_rewrite_prop(d, rows, sum, za_sym, q_lt_rows, &|d, t| NatOps::lt(d, q, t));

    let aux = d.lemma(p.pairs_of_is_echelon_aux, &[e, rows, cols, q, rows, zero_n]);
    let proof = d.apply(aux, &[zero_le_q, hq, in_fuel, hyp]);

    let ty = {
        let with_hq = d.pi_fv(hq_fv, bound, goal);
        let over_q = d.pi_fv(q_fv, nat, with_hq);
        let over_hyp = d.pi_fv(hyp_fv, hyp_ty, over_q);
        let over_cols = d.pi_fv(cols_fv, nat, over_hyp);
        let over_rows = d.pi_fv(rows_fv, nat, over_cols);
        d.pi_fv(e_fv, mty, over_rows)
    };
    let value = {
        let with_hq = d.lam_fv(hq_fv, bound, proof);
        let over_q = d.lam_fv(q_fv, nat, with_hq);
        let over_hyp = d.lam_fv(hyp_fv, hyp_ty, over_q);
        let over_cols = d.lam_fv(cols_fv, nat, over_hyp);
        let over_rows = d.lam_fv(rows_fv, nat, over_cols);
        d.lam_fv(e_fv, mty, over_rows)
    };
    d.declare_theorem(p.pairs_of_is_echelon, ty, value)
}

/// Admit `Rat.leadingIndex_strict_below : ∀ E rows cols,
/// (∀ t, Lt (succ t) rows → Eq Bool (echelonStepOk (leadingIndex E t cols)
///        (leadingIndex E (succ t) cols) cols) true) →
/// ∀ r, Lt r rows → Lt (leadingIndex E r cols) cols →
/// ∀ q, Lt q r → Lt (leadingIndex E q cols) (leadingIndex E r cols)`.
///
/// *Adjacent strict increase, extended to distance.*
///
/// **The induction is on the UPPER row, not on the distance between the two.**
/// That is what keeps `Nat.add` and `Nat.sub` out of the statement: the motive
/// is `∀ q, Lt q r → …`, the successor step splits `Le q r'` into `Lt q r'`
/// (the induction hypothesis) and `Eq q r'` (the adjacent pair, verbatim), and
/// no arithmetic on indices is ever formed. A distance induction would need
/// `r = q + d` and then either a subtraction or an existential.
///
/// The hypothesis `Lt (leadingIndex E r cols) cols` travels DOWN the chain
/// rather than being assumed at each level: at `succ r'` it plus the adjacent
/// pair give `Lt (leadingIndex E r' cols) (leadingIndex E (succ r') cols)`
/// through `Rat.lt_of_echelonStepOk`, and that is what re-establishes it at
/// `r'`.
fn declare_leading_index_strict_below(
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

    let pairs_ty = {
        let t_fv = d.fresh_fvar();
        let t = d.kernel().fvar(t_fv);
        let st = d.succ(t);
        let bound = NatOps::lt(d, st, rows);
        let concl = pair_ok_at(d, p, e, cols, t);
        let body = d.arrow(bound, concl);
        d.pi_fv(t_fv, nat, body)
    };
    let pairs_fv = d.fresh_fvar();
    let pairs = d.kernel().fvar(pairs_fv);

    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let nat_i = d.nat_ty();
        let in_rows = NatOps::lt(d, x, rows);
        let lx = rleading_index(d, p, e, x, cols);
        let in_cols = NatOps::lt(d, lx, cols);
        let q_fv = d.fresh_fvar();
        let q = d.kernel().fvar(q_fv);
        let below = NatOps::lt(d, q, x);
        let lq = rleading_index(d, p, e, q, cols);
        let concl = NatOps::lt(d, lq, lx);
        let with_below = d.arrow(below, concl);
        let over_q = d.pi_fv(q_fv, nat_i, with_below);
        let a2 = d.arrow(in_cols, over_q);
        d.arrow(in_rows, a2)
    };

    let zero_n = d.zero();
    let base = |d: &mut IntDev<'_>| -> ExprId {
        let nat_i = d.nat_ty();
        let in_rows = NatOps::lt(d, zero_n, rows);
        let l0 = rleading_index(d, p, e, zero_n, cols);
        let in_cols = NatOps::lt(d, l0, cols);
        let h1_fv = d.fresh_fvar();
        let h2_fv = d.fresh_fvar();
        let q_fv = d.fresh_fvar();
        let q = d.kernel().fvar(q_fv);
        let below = NatOps::lt(d, q, zero_n);
        let hb_fv = d.fresh_fvar();
        let hb = d.kernel().fvar(hb_fv);
        let lq = rleading_index(d, p, e, q, cols);
        let concl = NatOps::lt(d, lq, l0);
        let not_succ_le_zero = d.prelude().not_succ_le_zero;
        let refutation = d.lemma(not_succ_le_zero, &[q]);
        let contradiction = d.apply(refutation, &[hb]);
        let body = absurd(d, concl, contradiction);
        let with_hb = d.lam_fv(hb_fv, below, body);
        let over_q = d.lam_fv(q_fv, nat_i, with_hb);
        let with_h2 = d.lam_fv(h2_fv, in_cols, over_q);
        d.lam_fv(h1_fv, in_rows, with_h2)
    };

    let step = |d: &mut IntDev<'_>, r: ExprId, ih: ExprId| -> ExprId {
        let nat_i = d.nat_ty();
        let sr = d.succ(r);
        let in_rows = NatOps::lt(d, sr, rows);
        let lsr = rleading_index(d, p, e, sr, cols);
        let in_cols = NatOps::lt(d, lsr, cols);
        let h1_fv = d.fresh_fvar();
        let h1 = d.kernel().fvar(h1_fv);
        let h2_fv = d.fresh_fvar();
        let h2 = d.kernel().fvar(h2_fv);

        let lr = rleading_index(d, p, e, r, cols);
        let pair = d.apply(pairs, &[r, h1]);
        let adjacent = d.lemma(p.lt_of_echelon_step_ok, &[lr, lsr, cols, pair, h2]);
        let lsr_le_cols = le_of_lt(d, lsr, cols, h2);
        let lt_of_lt_of_le = d.prelude().lt_of_lt_of_le;
        let lr_lt_cols = d.lemma(lt_of_lt_of_le, &[lr, lsr, cols, adjacent, lsr_le_cols]);
        let le_succ = d.prelude().le_succ;
        let le_trans = d.prelude().le_trans;
        let ssr = d.succ(sr);
        let up = d.lemma(le_succ, &[sr]);
        let r_lt_rows = d.lemma(le_trans, &[sr, ssr, rows, up, h1]);

        let q_fv = d.fresh_fvar();
        let q = d.kernel().fvar(q_fv);
        let below = NatOps::lt(d, q, sr);
        let hb_fv = d.fresh_fvar();
        let hb = d.kernel().fvar(hb_fv);
        let lq = rleading_index(d, p, e, q, cols);
        let concl = NatOps::lt(d, lq, lsr);

        let le_of_succ_le_succ = d.prelude().le_of_succ_le_succ;
        let q_le_r = d.lemma(le_of_succ_le_succ, &[q, r, hb]);
        let lt_or_eq_of_le = d.prelude().lt_or_eq_of_le;
        let split = d.lemma(lt_or_eq_of_le, &[q, r, q_le_r]);
        let lt_ty = NatOps::lt(d, q, r);
        let eq_ty = d.eq(q, r);

        let strictly_above = {
            let hx_fv = d.fresh_fvar();
            let hx = d.kernel().fvar(hx_fv);
            let chained = d.apply(ih, &[r_lt_rows, lr_lt_cols, q, hx]);
            let lr_le_lsr = le_of_lt(d, lr, lsr, adjacent);
            let joined = d.lemma(lt_of_lt_of_le, &[lq, lr, lsr, chained, lr_le_lsr]);
            d.lam_fv(hx_fv, lt_ty, joined)
        };
        let the_adjacent_one = {
            let he_fv = d.fresh_fvar();
            let he = d.kernel().fvar(he_fv);
            let back = NatOps::symm(d, q, r, he);
            let moved = nat_rewrite_prop(d, r, q, back, adjacent, &|d, t| {
                let lt_ = rleading_index(d, p, e, t, cols);
                let right = rleading_index(d, p, e, sr, cols);
                NatOps::lt(d, lt_, right)
            });
            d.lam_fv(he_fv, eq_ty, moved)
        };

        let chosen = or_cases(
            d,
            lt_ty,
            eq_ty,
            concl,
            strictly_above,
            the_adjacent_one,
            split,
        );
        let with_hb = d.lam_fv(hb_fv, below, chosen);
        let over_q = d.lam_fv(q_fv, nat_i, with_hb);
        let with_h2 = d.lam_fv(h2_fv, in_cols, over_q);
        d.lam_fv(h1_fv, in_rows, with_h2)
    };

    let r_fv = d.fresh_fvar();
    let r = d.kernel().fvar(r_fv);
    let proof = d.induct(&motive, &base, &step, r);
    let stmt = motive(d, r);

    let ty = {
        let over_r = d.pi_fv(r_fv, nat, stmt);
        let over_pairs = d.pi_fv(pairs_fv, pairs_ty, over_r);
        let over_cols = d.pi_fv(cols_fv, nat, over_pairs);
        let over_rows = d.pi_fv(rows_fv, nat, over_cols);
        d.pi_fv(e_fv, mty, over_rows)
    };
    let value = {
        let over_r = d.lam_fv(r_fv, nat, proof);
        let over_pairs = d.lam_fv(pairs_fv, pairs_ty, over_r);
        let over_cols = d.lam_fv(cols_fv, nat, over_pairs);
        let over_rows = d.lam_fv(rows_fv, nat, over_cols);
        d.lam_fv(e_fv, mty, over_rows)
    };
    d.declare_theorem(p.leading_index_strict_below, ty, value)
}

/// Admit `Rat.pivotRowSearchAux_eq_of_first : ∀ E rows cols j r fuel start,
/// Le start r → Lt r rows → Lt r (Nat.add start fuel) →
/// (∀ q, Le start q → Lt q r → Not (Eq Nat (leadingIndex E q cols) j)) →
/// Eq Nat (leadingIndex E r cols) j →
/// Eq Nat (pivotRowSearchAux E rows cols j fuel start) r`.
///
/// The same shape as `Rat.leadingIndexAux_eq_of_first_nonzero`: *nothing before
/// it matches, it matches, and the fuel reaches it.* The bound is forced —
/// the scan's exhaustion answer is `rows` and `r` is in range, so an exhausted
/// scan falsifies the conclusion.
fn declare_pivot_row_search_aux_eq_of_first(
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
    let r_fv = d.fresh_fvar();
    let r = d.kernel().fvar(r_fv);

    let hyps = |d: &mut IntDev<'_>, start: ExprId, x: ExprId| -> [ExprId; 5] {
        let nat_i = d.nat_ty();
        let h1 = NatOps::le(d, start, r);
        let h2 = NatOps::lt(d, r, rows);
        let sum = NatOps::add(d, start, x);
        let h3 = NatOps::lt(d, r, sum);
        let h4 = {
            let q_fv = d.fresh_fvar();
            let q = d.kernel().fvar(q_fv);
            let lo = NatOps::le(d, start, q);
            let hi = NatOps::lt(d, q, r);
            let lq = rleading_index(d, p, e, q, cols);
            let eq = d.eq(lq, j);
            let ne = d.not(eq);
            let a2 = d.arrow(hi, ne);
            let a1 = d.arrow(lo, a2);
            d.pi_fv(q_fv, nat_i, a1)
        };
        let h5 = {
            let lr = rleading_index(d, p, e, r, cols);
            d.eq(lr, j)
        };
        [h1, h2, h3, h4, h5]
    };

    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let nat_i = d.nat_ty();
        let s_fv = d.fresh_fvar();
        let start = d.kernel().fvar(s_fv);
        let tys = hyps(d, start, x);
        let found = d.const_app(p.pivot_row_search_aux, &[e, rows, cols, j, x, start]);
        let concl = d.eq(found, r);
        let mut body = concl;
        for ty in tys.into_iter().rev() {
            body = d.arrow(ty, body);
        }
        d.pi_fv(s_fv, nat_i, body)
    };

    let bind = |d: &mut IntDev<'_>,
                start: ExprId,
                x: ExprId,
                body: &dyn Fn(&mut IntDev<'_>, [ExprId; 5]) -> ExprId|
     -> ExprId {
        let tys = hyps(d, start, x);
        let mut fvs = [d.fresh_fvar(); 5];
        for slot in &mut fvs {
            *slot = d.fresh_fvar();
        }
        let mut vals = [r; 5];
        for (slot, fv) in vals.iter_mut().zip(fvs) {
            *slot = d.kernel().fvar(fv);
        }
        let mut inner = body(d, vals);
        for i in (0..5).rev() {
            inner = d.lam_fv(fvs[i], tys[i], inner);
        }
        inner
    };

    let zero_n = d.zero();
    let base = |d: &mut IntDev<'_>| -> ExprId {
        let nat_i = d.nat_ty();
        let s_fv = d.fresh_fvar();
        let start = d.kernel().fvar(s_fv);
        let body = bind(d, start, zero_n, &|d, hs| {
            let found = d.const_app(p.pivot_row_search_aux, &[e, rows, cols, j, zero_n, start]);
            let concl = d.eq(found, r);
            let lt_of_lt_of_le = d.prelude().lt_of_lt_of_le;
            let self_lt = d.lemma(lt_of_lt_of_le, &[r, start, r, hs[2], hs[0]]);
            let lt_irrefl = d.prelude().lt_irrefl;
            let contradiction = d.lemma(lt_irrefl, &[r, self_lt]);
            absurd(d, concl, contradiction)
        });
        d.lam_fv(s_fv, nat_i, body)
    };

    let step = |d: &mut IntDev<'_>, n: ExprId, ih: ExprId| -> ExprId {
        let nat_i = d.nat_ty();
        let s_fv = d.fresh_fvar();
        let start = d.kernel().fvar(s_fv);
        let sn = d.succ(n);
        let ss = d.succ(start);

        let body = bind(d, start, sn, &|d, hs| {
            let l_start = rleading_index(d, p, e, start, cols);
            let hit = NatOps::beq(d, l_start, j);
            let rec_next = d.const_app(p.pivot_row_search_aux, &[e, rows, cols, j, n, ss]);
            let oor = NatOps::ble(d, rows, start);

            let true_ = d.bool_true();
            let false_ = d.bool_false();

            let inner_shape = |d: &mut IntDev<'_>, y: ExprId| -> ExprId {
                let nat_j = d.nat_ty();
                let sel = bool_select_at(d, nat_j, y, start, rec_next);
                d.eq(sel, r)
            };
            let outer_shape = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
                let nat_j = d.nat_ty();
                let inner = bool_select_at(d, nat_j, hit, start, rec_next);
                let sel = bool_select_at(d, nat_j, x, rows, inner);
                d.eq(sel, r)
            };

            let goal = outer_shape(d, oor);
            let oor_true_ty = d.bool_eq(oor, true_);
            let oor_false_ty = d.bool_eq(oor, false_);

            // `Le start r` and `Lt r rows` put `start` strictly inside, so the
            // out-of-range branch is refuted.
            let refute_oor = {
                let ht_fv = d.fresh_fvar();
                let ht = d.kernel().fvar(ht_fv);
                let le_of_ble = d.prelude().le_of_ble_eq_true;
                let rows_le_start = d.lemma(le_of_ble, &[rows, start, ht]);
                let lt_of_le_of_lt = d.prelude().lt_of_le_of_lt;
                let start_lt_rows = d.lemma(lt_of_le_of_lt, &[start, r, rows, hs[0], hs[1]]);
                let lt_of_lt_of_le = d.prelude().lt_of_lt_of_le;
                let self_lt = d.lemma(
                    lt_of_lt_of_le,
                    &[start, rows, start, start_lt_rows, rows_le_start],
                );
                let lt_irrefl = d.prelude().lt_irrefl;
                let contradiction = d.lemma(lt_irrefl, &[start, self_lt]);
                let inner = absurd(d, goal, contradiction);
                d.lam_fv(ht_fv, oor_true_ty, inner)
            };

            let scanning = {
                let hf_fv = d.fresh_fvar();
                let hf = d.kernel().fvar(hf_fv);
                let inner_goal = inner_shape(d, hit);
                let hit_true_ty = d.bool_eq(hit, true_);
                let hit_false_ty = d.bool_eq(hit, false_);

                // It matches here, so `start` must BE `r`: anything strictly
                // before `r` was excluded by hypothesis.
                let matched = {
                    let hb_fv = d.fresh_fvar();
                    let hb = d.kernel().fvar(hb_fv);
                    let target = d.eq(start, r);
                    let eq_of_beq = d.prelude().eq_of_beq_eq_true;
                    let l_eq_j = d.lemma(eq_of_beq, &[l_start, j, hb]);
                    let lt_or_eq_of_le = d.prelude().lt_or_eq_of_le;
                    let split = d.lemma(lt_or_eq_of_le, &[start, r, hs[0]]);
                    let lt_ty = NatOps::lt(d, start, r);
                    let eq_ty = d.eq(start, r);
                    let le_refl = d.prelude().le_refl_thm;
                    let start_le_start = d.lemma(le_refl, &[start]);
                    let too_early = {
                        let hx_fv = d.fresh_fvar();
                        let hx = d.kernel().fvar(hx_fv);
                        let excluded = d.apply(hs[3], &[start, start_le_start, hx]);
                        let contradiction = d.apply(excluded, &[l_eq_j]);
                        let inner = absurd(d, target, contradiction);
                        d.lam_fv(hx_fv, lt_ty, inner)
                    };
                    let exactly = {
                        let he_fv = d.fresh_fvar();
                        let he = d.kernel().fvar(he_fv);
                        d.lam_fv(he_fv, eq_ty, he)
                    };
                    let chosen = or_cases(d, lt_ty, eq_ty, target, too_early, exactly, split);
                    let motive_y = d.bool_eq_motive(true_, &inner_shape);
                    let hb_sym = d.bool_symm(hit, true_, hb);
                    let moved = d.bool_transport(true_, motive_y, chosen, hit, hb_sym);
                    d.lam_fv(hb_fv, hit_true_ty, moved)
                };

                // It does not match here, so `start` is not `r` and the scan
                // moves on with every hypothesis re-established.
                let missed = {
                    let hb_fv = d.fresh_fvar();
                    let hb = d.kernel().fvar(hb_fv);

                    // `start = r` would make the test succeed, and it did not.
                    let start_ne_r = {
                        let eq_ty = d.eq(start, r);
                        let x_fv = d.fresh_fvar();
                        let x = d.kernel().fvar(x_fv);
                        let back = NatOps::symm(d, start, r, x);
                        let l_eq_j = nat_rewrite_prop(d, r, start, back, hs[4], &|d, t| {
                            let lt_ = rleading_index(d, p, e, t, cols);
                            d.eq(lt_, j)
                        });
                        let beq_true = d.prelude().beq_eq_true_of_eq;
                        let would_hit = d.lemma(beq_true, &[l_start, j, l_eq_j]);
                        let false_v = d.bool_false();
                        let true_v = d.bool_true();
                        let flipped = d.bool_symm(hit, false_v, hb);
                        let joined = d.bool_trans(false_v, hit, true_v, flipped, would_hit);
                        let contradiction = refute_false_true(d, joined);
                        d.lam_fv(x_fv, eq_ty, contradiction)
                    };

                    let lt_or_eq_of_le = d.prelude().lt_or_eq_of_le;
                    let split = d.lemma(lt_or_eq_of_le, &[start, r, hs[0]]);
                    let lt_ty = NatOps::lt(d, start, r);
                    let eq_ty = d.eq(start, r);
                    let target = inner_shape(d, false_);

                    let move_on = {
                        let hx_fv = d.fresh_fvar();
                        let hx = d.kernel().fvar(hx_fv);
                        // `Le (succ start) r` IS `Lt start r`, so `hx` is the
                        // next level's lower bound without conversion.
                        let add_s_n = NatOps::add(d, start, n);
                        let s_add = d.succ(add_s_n);
                        let add_ss_n = NatOps::add(d, ss, n);
                        let succ_add = d.prelude().succ_add;
                        let sa = d.lemma(succ_add, &[start, n]);
                        let sa_sym = NatOps::symm(d, add_ss_n, s_add, sa);
                        let next_fuel =
                            nat_rewrite_prop(d, s_add, add_ss_n, sa_sym, hs[2], &|d, t| {
                                NatOps::lt(d, r, t)
                            });
                        let next_excluded = {
                            let nat_k = d.nat_ty();
                            let q_fv = d.fresh_fvar();
                            let q = d.kernel().fvar(q_fv);
                            let lo = NatOps::le(d, ss, q);
                            let hi = NatOps::lt(d, q, r);
                            let a_fv = d.fresh_fvar();
                            let a = d.kernel().fvar(a_fv);
                            let b_fv = d.fresh_fvar();
                            let b = d.kernel().fvar(b_fv);
                            let le_succ = d.prelude().le_succ;
                            let le_trans = d.prelude().le_trans;
                            let up = d.lemma(le_succ, &[start]);
                            let start_le_q = d.lemma(le_trans, &[start, ss, q, up, a]);
                            let applied = d.apply(hs[3], &[q, start_le_q, b]);
                            let with_b = d.lam_fv(b_fv, hi, applied);
                            let with_a = d.lam_fv(a_fv, lo, with_b);
                            d.lam_fv(q_fv, nat_k, with_a)
                        };
                        let recursed =
                            d.apply(ih, &[ss, hx, hs[1], next_fuel, next_excluded, hs[4]]);
                        d.lam_fv(hx_fv, lt_ty, recursed)
                    };
                    let impossible = {
                        let he_fv = d.fresh_fvar();
                        let he = d.kernel().fvar(he_fv);
                        let contradiction = d.apply(start_ne_r, &[he]);
                        let inner = absurd(d, target, contradiction);
                        d.lam_fv(he_fv, eq_ty, inner)
                    };
                    let chosen = or_cases(d, lt_ty, eq_ty, target, move_on, impossible, split);
                    let motive_y = d.bool_eq_motive(false_, &inner_shape);
                    let hb_sym = d.bool_symm(hit, false_, hb);
                    let moved = d.bool_transport(false_, motive_y, chosen, hit, hb_sym);
                    d.lam_fv(hb_fv, hit_false_ty, moved)
                };

                let split = bool_cases(d, hit);
                let chosen = or_cases(
                    d,
                    hit_true_ty,
                    hit_false_ty,
                    inner_goal,
                    matched,
                    missed,
                    split,
                );
                let motive_x = d.bool_eq_motive(false_, &outer_shape);
                let hf_sym = d.bool_symm(oor, false_, hf);
                let moved = d.bool_transport(false_, motive_x, chosen, oor, hf_sym);
                d.lam_fv(hf_fv, oor_false_ty, moved)
            };

            let split = bool_cases(d, oor);
            or_cases(
                d,
                oor_true_ty,
                oor_false_ty,
                goal,
                refute_oor,
                scanning,
                split,
            )
        });
        d.lam_fv(s_fv, nat_i, body)
    };

    let fuel_fv = d.fresh_fvar();
    let fuel = d.kernel().fvar(fuel_fv);
    let proof = d.induct(&motive, &base, &step, fuel);
    let stmt = motive(d, fuel);

    let ty = {
        let over_fuel = d.pi_fv(fuel_fv, nat, stmt);
        let over_r = d.pi_fv(r_fv, nat, over_fuel);
        let over_j = d.pi_fv(j_fv, nat, over_r);
        let over_cols = d.pi_fv(cols_fv, nat, over_j);
        let over_rows = d.pi_fv(rows_fv, nat, over_cols);
        d.pi_fv(e_fv, mty, over_rows)
    };
    let value = {
        let over_fuel = d.lam_fv(fuel_fv, nat, proof);
        let over_r = d.lam_fv(r_fv, nat, over_fuel);
        let over_j = d.lam_fv(j_fv, nat, over_r);
        let over_cols = d.lam_fv(cols_fv, nat, over_j);
        let over_rows = d.lam_fv(rows_fv, nat, over_cols);
        d.lam_fv(e_fv, mty, over_rows)
    };
    d.declare_theorem(p.pivot_row_search_aux_eq_of_first, ty, value)
}

/// Admit `Rat.pivotRowOfCol_eq_of_first : ∀ E rows cols j r, Lt r rows →
/// (∀ q, Lt q r → Not (Eq Nat (leadingIndex E q cols) j)) →
/// Eq Nat (leadingIndex E r cols) j →
/// Eq Nat (pivotRowOfCol E rows cols j) r`.
fn declare_pivot_row_of_col_eq_of_first(
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
    let r_fv = d.fresh_fvar();
    let r = d.kernel().fvar(r_fv);

    let h1_ty = NatOps::lt(d, r, rows);
    let h2_ty = {
        let q_fv = d.fresh_fvar();
        let q = d.kernel().fvar(q_fv);
        let hi = NatOps::lt(d, q, r);
        let lq = rleading_index(d, p, e, q, cols);
        let eq = d.eq(lq, j);
        let ne = d.not(eq);
        let body = d.arrow(hi, ne);
        d.pi_fv(q_fv, nat, body)
    };
    let h3_ty = {
        let lr = rleading_index(d, p, e, r, cols);
        d.eq(lr, j)
    };

    let h1_fv = d.fresh_fvar();
    let h1 = d.kernel().fvar(h1_fv);
    let h2_fv = d.fresh_fvar();
    let h2 = d.kernel().fvar(h2_fv);
    let h3_fv = d.fresh_fvar();
    let h3 = d.kernel().fvar(h3_fv);

    let found = d.const_app(p.pivot_row_of_col, &[e, rows, cols, j]);
    let concl = d.eq(found, r);

    let zero_n = d.zero();
    let zero_le = d.prelude().zero_le;
    let zero_le_r = d.lemma(zero_le, &[r]);
    let sum = NatOps::add(d, zero_n, rows);
    let zero_add = d.prelude().zero_add;
    let za = d.lemma(zero_add, &[rows]);
    let za_sym = NatOps::symm(d, sum, rows, za);
    let in_fuel = nat_rewrite_prop(d, rows, sum, za_sym, h1, &|d, t| NatOps::lt(d, r, t));
    let widened = {
        let q_fv = d.fresh_fvar();
        let q = d.kernel().fvar(q_fv);
        let lo = NatOps::le(d, zero_n, q);
        let hi = NatOps::lt(d, q, r);
        let a_fv = d.fresh_fvar();
        let b_fv = d.fresh_fvar();
        let b = d.kernel().fvar(b_fv);
        let applied = d.apply(h2, &[q, b]);
        let with_b = d.lam_fv(b_fv, hi, applied);
        let with_a = d.lam_fv(a_fv, lo, with_b);
        d.lam_fv(q_fv, nat, with_a)
    };
    let aux = d.lemma(
        p.pivot_row_search_aux_eq_of_first,
        &[e, rows, cols, j, r, rows, zero_n],
    );
    let proof = d.apply(aux, &[zero_le_r, h1, in_fuel, widened, h3]);

    let ty = {
        let f3 = d.pi_fv(h3_fv, h3_ty, concl);
        let f2 = d.pi_fv(h2_fv, h2_ty, f3);
        let f1 = d.pi_fv(h1_fv, h1_ty, f2);
        let over_r = d.pi_fv(r_fv, nat, f1);
        let over_j = d.pi_fv(j_fv, nat, over_r);
        let over_cols = d.pi_fv(cols_fv, nat, over_j);
        let over_rows = d.pi_fv(rows_fv, nat, over_cols);
        d.pi_fv(e_fv, mty, over_rows)
    };
    let value = {
        let f3 = d.lam_fv(h3_fv, h3_ty, proof);
        let f2 = d.lam_fv(h2_fv, h2_ty, f3);
        let f1 = d.lam_fv(h1_fv, h1_ty, f2);
        let over_r = d.lam_fv(r_fv, nat, f1);
        let over_j = d.lam_fv(j_fv, nat, over_r);
        let over_cols = d.lam_fv(cols_fv, nat, over_j);
        let over_rows = d.lam_fv(rows_fv, nat, over_cols);
        d.lam_fv(e_fv, mty, over_rows)
    };
    d.declare_theorem(p.pivot_row_of_col_eq_of_first, ty, value)
}

/// The pivot-section hypothesis, at a matrix `e` — ADR-1562 §2's equation,
/// written exactly as the three `_of_pivotSection` theorems bind it.
fn pivot_section_at(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    e: ExprId,
    rows: ExprId,
    cols: ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let r_fv = d.fresh_fvar();
    let r = d.kernel().fvar(r_fv);
    let bound = NatOps::lt(d, r, rows);
    let nz = rnonzero_row_b(d, p, e, cols, r);
    let true_ = d.bool_true();
    let selected = d.bool_eq(nz, true_);
    let col = d.const_app(p.pivot_col_of_row, &[e, cols, r]);
    let back = d.const_app(p.pivot_row_of_col, &[e, rows, cols, col]);
    let concl = d.eq(back, r);
    let a2 = d.arrow(selected, concl);
    let a1 = d.arrow(bound, a2);
    d.pi_fv(r_fv, nat, a1)
}

/// Admit `Rat.pivotSection_of_isEchelon : ∀ E rows cols,
/// Eq Bool (isEchelon E rows cols) true → (the pivot section at E)`.
///
/// **The implication ADR-1562 §2 identified and ADR-1574 made derivable.**
/// `nonzeroRowB E cols r = true` is `Nat.ble (succ (leadingIndex E r cols))
/// cols = true`, i.e. the row leads strictly inside the width, which is exactly
/// the hypothesis `Rat.leadingIndex_strict_below` needs to run the chain down
/// from `r`. Every row above `r` then leads strictly left of it, so none of
/// them can match, and `Rat.pivotRowOfCol_eq_of_first` answers `r`.
fn declare_pivot_section_of_is_echelon(
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

    let scanned = d.const_app(p.is_echelon, &[e, rows, cols]);
    let true_ = d.bool_true();
    let hyp_ty = d.bool_eq(scanned, true_);
    let hyp_fv = d.fresh_fvar();
    let hyp = d.kernel().fvar(hyp_fv);

    let concl = pivot_section_at(d, p, e, rows, cols);

    let pairs = d.lemma(p.pairs_of_is_echelon, &[e, rows, cols, hyp]);

    let r_fv = d.fresh_fvar();
    let r = d.kernel().fvar(r_fv);
    let bound = NatOps::lt(d, r, rows);
    let nz = rnonzero_row_b(d, p, e, cols, r);
    let selected_ty = d.bool_eq(nz, true_);
    let hb_fv = d.fresh_fvar();
    let hb = d.kernel().fvar(hb_fv);
    let hs_fv = d.fresh_fvar();
    let hs = d.kernel().fvar(hs_fv);

    let lr = rleading_index(d, p, e, r, cols);
    let slr = d.succ(lr);
    // `nonzeroRowB E cols r` IS `Nat.ble (succ (leadingIndex E r cols)) cols`.
    let le_of_ble = d.prelude().le_of_ble_eq_true;
    let lr_lt_cols = d.lemma(le_of_ble, &[slr, cols, hs]);

    let chain = d.lemma(
        p.leading_index_strict_below,
        &[e, rows, cols, pairs, r, hb, lr_lt_cols],
    );

    let excluded = {
        let q_fv = d.fresh_fvar();
        let q = d.kernel().fvar(q_fv);
        let hi = NatOps::lt(d, q, r);
        let hq_fv = d.fresh_fvar();
        let hq = d.kernel().fvar(hq_fv);
        let lq = rleading_index(d, p, e, q, cols);
        let strict = d.apply(chain, &[q, hq]);
        let ne = ne_of_lt(d, lq, lr, strict);
        let with_hq = d.lam_fv(hq_fv, hi, ne);
        d.lam_fv(q_fv, nat, with_hq)
    };

    let refl_lr = d.refl(lr);
    let answer = d.lemma(
        p.pivot_row_of_col_eq_of_first,
        &[e, rows, cols, lr, r, hb, excluded, refl_lr],
    );

    let ty = {
        let over_hyp = d.pi_fv(hyp_fv, hyp_ty, concl);
        let over_cols = d.pi_fv(cols_fv, nat, over_hyp);
        let over_rows = d.pi_fv(rows_fv, nat, over_cols);
        d.pi_fv(e_fv, mty, over_rows)
    };
    let value = {
        let with_hs = d.lam_fv(hs_fv, selected_ty, answer);
        let with_hb = d.lam_fv(hb_fv, bound, with_hs);
        let over_r = d.lam_fv(r_fv, nat, with_hb);
        let over_hyp = d.lam_fv(hyp_fv, hyp_ty, over_r);
        let over_cols = d.lam_fv(cols_fv, nat, over_hyp);
        let over_rows = d.lam_fv(rows_fv, nat, over_cols);
        d.lam_fv(e_fv, mty, over_rows)
    };
    d.declare_theorem(p.pivot_section_of_is_echelon, ty, value)
}

/// The section hypothesis at `rowEchelon M rows cols`, discharged.
fn section_for(d: &mut IntDev<'_>, p: RatPrelude, m: ExprId, rows: ExprId, cols: ExprId) -> ExprId {
    let e = d.const_app(p.row_echelon, &[m, rows, cols]);
    let echelon = d.lemma(p.row_echelon_is_echelon, &[m, rows, cols]);
    d.lemma(p.pivot_section_of_is_echelon, &[e, rows, cols, echelon])
}

/// Admit `Rat.rank_eq_rankCols : ∀ M rows cols,
/// Eq Nat (rank M rows cols) (rankCols M rows cols)` — **unconditional.**
fn declare_rank_eq_rank_cols(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let mty = mat_ty(d);

    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let rows_fv = d.fresh_fvar();
    let rows = d.kernel().fvar(rows_fv);
    let cols_fv = d.fresh_fvar();
    let cols = d.kernel().fvar(cols_fv);

    let lhs = d.const_app(p.rank, &[m, rows, cols]);
    let rhs = d.const_app(p.rank_cols, &[m, rows, cols]);
    let concl = d.eq(lhs, rhs);

    let section = section_for(d, p, m, rows, cols);
    let proof = d.lemma(
        p.rank_eq_rank_cols_of_pivot_section,
        &[m, rows, cols, section],
    );

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
    d.declare_theorem(p.rank_eq_rank_cols, ty, value)
}

/// Admit `Rat.rank_le_cols : ∀ M rows cols, Le (rank M rows cols) cols` —
/// **unconditional**, the bound ADR-1555 stated as open.
fn declare_rank_le_cols(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let mty = mat_ty(d);

    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let rows_fv = d.fresh_fvar();
    let rows = d.kernel().fvar(rows_fv);
    let cols_fv = d.fresh_fvar();
    let cols = d.kernel().fvar(cols_fv);

    let rk = d.const_app(p.rank, &[m, rows, cols]);
    let concl = NatOps::le(d, rk, cols);

    let section = section_for(d, p, m, rows, cols);
    let proof = d.lemma(p.rank_le_cols_of_pivot_section, &[m, rows, cols, section]);

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
    d.declare_theorem(p.rank_le_cols, ty, value)
}

/// Admit `Rat.rank_nullity_rows : ∀ M rows cols,
/// Eq Nat (Nat.add (rank M rows cols) (nullity M rows cols)) cols` —
/// **rank-nullity in the ROW form, unconditional.**
fn declare_rank_nullity_rows(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let mty = mat_ty(d);

    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let rows_fv = d.fresh_fvar();
    let rows = d.kernel().fvar(rows_fv);
    let cols_fv = d.fresh_fvar();
    let cols = d.kernel().fvar(cols_fv);

    let rk = d.const_app(p.rank, &[m, rows, cols]);
    let nl = d.const_app(p.nullity, &[m, rows, cols]);
    let sum = NatOps::add(d, rk, nl);
    let concl = d.eq(sum, cols);

    let section = section_for(d, p, m, rows, cols);
    let proof = d.lemma(
        p.rank_nullity_rows_of_pivot_section,
        &[m, rows, cols, section],
    );

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
    d.declare_theorem(p.rank_nullity_rows, ty, value)
}
