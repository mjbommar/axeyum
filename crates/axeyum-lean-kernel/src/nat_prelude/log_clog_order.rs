//! `Nat.log`/`Nat.clog` order mirrors: monotonicity in the second argument
//! (both the pointwise `_mono_right` form and the `Monotone`-bundle form),
//! and `Nat.clog_pos`.
//!
//! Both `log.rs` and `clog.rs` already carry the four boundary equations and
//! (for `log`) the fuel bound `logAux_le_fuel`. Monotonicity is a genuinely
//! harder tier: comparing `logAux b f n` and `logAux b g m` (or the `clog`
//! analogues) at DIFFERENT fuels and DIFFERENT values needs a lemma neither
//! file built — `Nat.div_le_div_right` — plus a case-split combinator
//! ([`le_of_bool_select_mono`]) generalizing `log.rs`'s private
//! `le_of_bool_select` from one shared test to two tests connected by an
//! implication, because the two sides' guards are no longer literally the
//! same expression once the values being compared differ.
//!
//! The two aux families guard their recursive step in OPPOSITE nesting
//! order (`clog.rs`'s module doc explains why): `logAux`'s outer cut is
//! `b ≤ n` (differs between the two sides being compared) with `2 ≤ b`
//! inner (same both sides); `clogAux`'s outer cut is `2 ≤ b` (same) with
//! `2 ≤ n` inner (differs). `le_of_bool_select_mono` does not care which
//! role a given cut plays — it is applied twice either way, once per
//! nesting level, with an identity implication where the test is literally
//! shared and a derived one where it is not.

use super::NatPrelude;
use super::helpers::iff_reverse;
use super::ops::{NatDev, NatOps};
use crate::BinderInfo;
use crate::KernelError;
use crate::expr::ExprId;

/// `Nat.logAux base fuel value` (mirrors `log.rs`'s private helper of the
/// same name and shape; not exported from that file).
fn log_aux(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    base: ExprId,
    fuel: ExprId,
    value: ExprId,
) -> ExprId {
    d.const_app(p.log_aux, &[base, fuel, value])
}

/// `Nat.log base value`.
fn log(d: &mut NatDev<'_>, p: &NatPrelude, base: ExprId, value: ExprId) -> ExprId {
    d.const_app(p.log, &[base, value])
}

/// `Nat.clogAux base fuel value` (mirrors `clog.rs`'s private helper).
fn clog_aux(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    base: ExprId,
    fuel: ExprId,
    value: ExprId,
) -> ExprId {
    d.const_app(p.clog_aux, &[base, fuel, value])
}

/// `Nat.clog base value`.
fn clog(d: &mut NatDev<'_>, p: &NatPrelude, base: ExprId, value: ExprId) -> ExprId {
    d.const_app(p.clog, &[base, value])
}

/// `False.elim`-style: `absurd : False` closes any `target`, via
/// `False.rec`. Mirrors the inline construction `log.rs`'s
/// `ble_eq_false_of_lt` uses.
fn false_elim(d: &mut NatDev<'_>, p: &NatPrelude, target: ExprId, absurd: ExprId) -> ExprId {
    let anon = d.anon_name();
    let false_ty = d.kernel().const_(p.logic.false_, vec![]);
    let motive = d.kernel().lam(anon, false_ty, target, BinderInfo::Default);
    let zero = d.kernel().level_zero();
    let false_rec = d.kernel().const_(p.logic.false_rec, vec![zero]);
    d.apply(false_rec, &[motive, absurd])
}

/// `Or.rec`-based case split (mirrors `log.rs`'s private `or_cases`, not
/// exported from that file).
#[allow(clippy::too_many_arguments)]
fn or_cases(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    left_ty: ExprId,
    right_ty: ExprId,
    goal: ExprId,
    left_minor: ExprId,
    right_minor: ExprId,
    proof: ExprId,
) -> ExprId {
    let anon = d.anon_name();
    let split_ty = d.const_app(p.logic.or, &[left_ty, right_ty]);
    let motive = d.kernel().lam(anon, split_ty, goal, BinderInfo::Default);
    let rec = d.kernel().const_(p.logic.or_rec, vec![]);
    d.apply(
        rec,
        &[left_ty, right_ty, motive, left_minor, right_minor, proof],
    )
}

/// `Le (bool_select_nat test1 on_true1 zero) (bool_select_nat test2 on_true2
/// zero)`, given that `test1 = true` implies `test2 = true`
/// (`to_test2_true`) and that the two "true" branches already relate
/// (`proof_true_true`, built independent of any `Bool` evidence — it must
/// typecheck unconditionally, the same requirement `log.rs`'s
/// `le_of_bool_select` places on ITS `proof_true`/`proof_false`).
///
/// Generalizes `le_of_bool_select` from a single shared test to two tests
/// connected by an implication: comparing `logAux`/`clogAux` at two
/// DIFFERENT values makes the two sides' guards two different expressions,
/// not one shared one, so `le_of_bool_select`'s single-`test` case split is
/// not enough on its own.
#[allow(clippy::too_many_arguments)]
fn le_of_bool_select_mono(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    test1: ExprId,
    test2: ExprId,
    on_true1: ExprId,
    on_true2: ExprId,
    to_test2_true: &dyn Fn(&mut NatDev<'_>, ExprId) -> ExprId,
    proof_true_true: ExprId,
) -> ExprId {
    let true_ = d.bool_true();
    let false_ = d.bool_false();
    let zero = d.zero();
    let bound_expr = d.bool_select_nat(test2, on_true2, zero);

    let is_true1 = d.bool_eq(test1, true_);
    let true_case = {
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let h2 = to_test2_true(d, h);

        // Reduce the RHS bound (`bool_select_nat test2 on_true2 zero`) to
        // `on_true2` using the DERIVED `test2 = true` evidence.
        let motive_rhs = d.bool_eq_motive(true_, &|d, x| {
            let selected = d.bool_select_nat(x, on_true2, zero);
            d.le(on_true1, selected)
        });
        let reversed2 = d.bool_symm(test2, true_, h2);
        let with_rhs_reduced =
            d.bool_transport(true_, motive_rhs, proof_true_true, test2, reversed2);

        // Reduce the LHS (`bool_select_nat test1 on_true1 zero`) to
        // `on_true1` using the GIVEN `test1 = true` evidence.
        let motive_lhs = d.bool_eq_motive(true_, &|d, x| {
            let selected = d.bool_select_nat(x, on_true1, zero);
            d.le(selected, bound_expr)
        });
        let reversed1 = d.bool_symm(test1, true_, h);
        let result = d.bool_transport(true_, motive_lhs, with_rhs_reduced, test1, reversed1);
        d.lam_fv(h_fv, is_true1, result)
    };

    let is_false1 = d.bool_eq(test1, false_);
    let false_case = {
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let zero_le_bound = d.lemma(p.zero_le, &[bound_expr]);
        let motive_lhs = d.bool_eq_motive(false_, &|d, x| {
            let selected = d.bool_select_nat(x, on_true1, zero);
            d.le(selected, bound_expr)
        });
        let reversed1 = d.bool_symm(test1, false_, h);
        let result = d.bool_transport(false_, motive_lhs, zero_le_bound, test1, reversed1);
        d.lam_fv(h_fv, is_false1, result)
    };

    let goal = {
        let lhs = d.bool_select_nat(test1, on_true1, zero);
        d.le(lhs, bound_expr)
    };
    let split = super::ops::bool_true_or_false(d, p, test1);
    or_cases(
        d, p, is_true1, is_false1, goal, true_case, false_case, split,
    )
}

/// `Nat.div_le_div_right : ∀ n m b, Le n m → Le (div n b) (div m b)`.
pub(super) fn declare_div_le_div_right(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.div_le_div_right, 3, &|d, values| {
        let (n, m, b) = (values[0], values[1], values[2]);
        let h_ty = d.le(n, m);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);

        let motive_at = move |d: &mut NatDev<'_>, base: ExprId| -> ExprId {
            let dn = d.div(n, base);
            let dm = d.div(m, base);
            d.le(dn, dm)
        };

        let at_zero = move |d: &mut NatDev<'_>| -> ExprId {
            let zero = d.zero();
            let div_n_0 = d.div(n, zero);
            let div_m_0 = d.div(m, zero);
            let dz_n = d.lemma(p.div_zero, &[n]);
            let dz_m = d.lemma(p.div_zero, &[m]);
            let base_le = d.lemma(p.le_refl, &[zero]);
            let sym_dz_m = d.symm(div_m_0, zero, dz_m);
            let motive1 = d.eq_motive(zero, &|d, x| d.le(zero, x));
            let r2 = d.transport(zero, motive1, base_le, div_m_0, sym_dz_m);
            let sym_dz_n = d.symm(div_n_0, zero, dz_n);
            let motive2 = d.eq_motive(zero, &move |d, x| d.le(x, div_m_0));
            d.transport(zero, motive2, r2, div_n_0, sym_dz_n)
        };

        let at_succ = move |d: &mut NatDev<'_>, bp: ExprId| -> ExprId {
            let base = d.succ(bp);
            let relation_m = d.lemma(p.div_mod_exec, &[bp, m]);
            let div_m_b = d.div(m, base);
            let mod_m_b = d.modulo(m, base);
            let succ_div_m_b = d.succ(div_m_b);
            let iff_fn = d.lemma(
                p.div_mod_lt_mul_iff,
                &[base, m, div_m_b, mod_m_b, succ_div_m_b],
            );
            let the_iff = d.apply(iff_fn, &[relation_m]);
            let mul_b_succ = d.mul(base, succ_div_m_b);
            let lt_ty1 = d.lt(m, mul_b_succ);
            let lt_ty2 = d.lt(div_m_b, succ_div_m_b);
            let self_lt = d.lemma(p.lt_succ_self, &[div_m_b]);
            let backward = iff_reverse(d, lt_ty1, lt_ty2, the_iff);
            let upper_m = d.apply(backward, &[self_lt]);
            let n_lt = d.lemma(p.lt_of_le_of_lt, &[n, m, mul_b_succ, h, upper_m]);
            let div_n_b = d.div(n, base);
            let lt_result = d.lemma(p.div_lt_of_lt_mul, &[n, base, succ_div_m_b, n_lt]);
            d.lemma(p.le_of_lt_succ, &[div_n_b, div_m_b, lt_result])
        };

        let body = super::ops::cases_zero_succ(d, b, &motive_at, &at_zero, &at_succ);
        let concl = motive_at(d, b);
        let stmt = d.arrow(h_ty, concl);
        let proof = d.lam_fv(h_fv, h_ty, body);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Nat.log_aux_mono : ∀ b f g n m, Le f g → Le n m → Le (logAux b f n)
/// (logAux b g m)`.
pub(super) fn declare_log_aux_mono(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    d.theorem(p.log_aux_mono, 2, &|d, values| {
        let (base, f) = (values[0], values[1]);
        let two = d.num(2);
        let base_exceeds_one = d.ble(two, base);

        let motive_at = move |d: &mut NatDev<'_>, fc: ExprId| -> ExprId {
            let g_fv = d.fresh_fvar();
            let g = d.kernel().fvar(g_fv);
            let n_fv = d.fresh_fvar();
            let n = d.kernel().fvar(n_fv);
            let m_fv = d.fresh_fvar();
            let m = d.kernel().fvar(m_fv);
            let hfg_ty = d.le(fc, g);
            let hnm_ty = d.le(n, m);
            let lhs = log_aux(d, &p, base, fc, n);
            let rhs = log_aux(d, &p, base, g, m);
            let concl = d.le(lhs, rhs);
            let with_hnm = d.arrow(hnm_ty, concl);
            let with_hfg = d.arrow(hfg_ty, with_hnm);
            let with_m = d.pi_fv(m_fv, nat, with_hfg);
            let with_n = d.pi_fv(n_fv, nat, with_m);
            d.pi_fv(g_fv, nat, with_n)
        };

        let base_case = move |d: &mut NatDev<'_>| -> ExprId {
            let g_fv = d.fresh_fvar();
            let g = d.kernel().fvar(g_fv);
            let n_fv = d.fresh_fvar();
            let m_fv = d.fresh_fvar();
            let m = d.kernel().fvar(m_fv);
            let zero = d.zero();
            let hfg_ty = d.le(zero, g);
            let n_stub = d.kernel().fvar(n_fv);
            let hnm_ty = d.le(n_stub, m);
            let hfg_fv = d.fresh_fvar();
            let hnm_fv = d.fresh_fvar();
            let rhs = log_aux(d, &p, base, g, m);
            let proof_body = d.lemma(p.zero_le, &[rhs]);
            let with_hnm = d.lam_fv(hnm_fv, hnm_ty, proof_body);
            let with_hfg = d.lam_fv(hfg_fv, hfg_ty, with_hnm);
            let with_m = d.lam_fv(m_fv, nat, with_hfg);
            let with_n = d.lam_fv(n_fv, nat, with_m);
            d.lam_fv(g_fv, nat, with_n)
        };

        let step_case = move |d: &mut NatDev<'_>, predecessor: ExprId, ih: ExprId| -> ExprId {
            let succ_f = d.succ(predecessor);

            let per_g_motive = move |d: &mut NatDev<'_>, gc: ExprId| -> ExprId {
                let n_fv = d.fresh_fvar();
                let n = d.kernel().fvar(n_fv);
                let m_fv = d.fresh_fvar();
                let m = d.kernel().fvar(m_fv);
                let hfg_ty = d.le(succ_f, gc);
                let hnm_ty = d.le(n, m);
                let lhs = log_aux(d, &p, base, succ_f, n);
                let rhs = log_aux(d, &p, base, gc, m);
                let concl = d.le(lhs, rhs);
                let with_hnm = d.arrow(hnm_ty, concl);
                let with_hfg = d.arrow(hfg_ty, with_hnm);
                let with_m = d.pi_fv(m_fv, nat, with_hfg);
                d.pi_fv(n_fv, nat, with_m)
            };

            let at_g_zero = move |d: &mut NatDev<'_>| -> ExprId {
                let n_fv = d.fresh_fvar();
                let n = d.kernel().fvar(n_fv);
                let m_fv = d.fresh_fvar();
                let m = d.kernel().fvar(m_fv);
                let zero = d.zero();
                let hfg_ty = d.le(succ_f, zero);
                let hnm_ty = d.le(n, m);
                let hfg_fv = d.fresh_fvar();
                let hfg = d.kernel().fvar(hfg_fv);
                let hnm_fv = d.fresh_fvar();
                let absurd = d.lemma(p.not_succ_le_zero, &[predecessor, hfg]);
                let lhs = log_aux(d, &p, base, succ_f, n);
                let rhs = log_aux(d, &p, base, zero, m);
                let target = d.le(lhs, rhs);
                let elim = false_elim(d, &p, target, absurd);
                let with_hnm = d.lam_fv(hnm_fv, hnm_ty, elim);
                let with_hfg = d.lam_fv(hfg_fv, hfg_ty, with_hnm);
                let with_m = d.lam_fv(m_fv, nat, with_hfg);
                d.lam_fv(n_fv, nat, with_m)
            };

            let at_g_succ = move |d: &mut NatDev<'_>, g_prime: ExprId| -> ExprId {
                let n_fv = d.fresh_fvar();
                let n = d.kernel().fvar(n_fv);
                let m_fv = d.fresh_fvar();
                let m = d.kernel().fvar(m_fv);
                let succ_g_prime = d.succ(g_prime);
                let hfg_ty = d.le(succ_f, succ_g_prime);
                let hnm_ty = d.le(n, m);
                let hfg_fv = d.fresh_fvar();
                let hfg = d.kernel().fvar(hfg_fv);
                let hnm_fv = d.fresh_fvar();
                let hnm = d.kernel().fvar(hnm_fv);

                let f_le_g_prime = d.lemma(p.le_of_succ_le_succ, &[predecessor, g_prime, hfg]);

                let quotient_n = d.div(n, base);
                let quotient_m = d.div(m, base);
                let hnm_div = d.lemma(p.div_le_div_right, &[n, m, base, hnm]);

                let ih_at_g = d.apply(
                    ih,
                    &[g_prime, quotient_n, quotient_m, f_le_g_prime, hnm_div],
                );
                let inner_lhs = log_aux(d, &p, base, predecessor, quotient_n);
                let inner_rhs = log_aux(d, &p, base, g_prime, quotient_m);
                let stepped_lhs = d.succ(inner_lhs);
                let stepped_rhs = d.succ(inner_rhs);
                let proof_stepped_le = d.lemma(p.le_succ_succ, &[inner_lhs, inner_rhs, ih_at_g]);

                let zero = d.zero();
                let inner_term_lhs = d.bool_select_nat(base_exceeds_one, stepped_lhs, zero);
                let inner_term_rhs = d.bool_select_nat(base_exceeds_one, stepped_rhs, zero);
                let inner_result = le_of_bool_select_mono(
                    d,
                    &p,
                    base_exceeds_one,
                    base_exceeds_one,
                    stepped_lhs,
                    stepped_rhs,
                    &|_d, h2| h2,
                    proof_stepped_le,
                );

                let base_fits_n = d.ble(base, n);
                let base_fits_m = d.ble(base, m);
                let to_test2_true = move |d: &mut NatDev<'_>, hh: ExprId| -> ExprId {
                    let ble_le_n = d.lemma(p.le_of_ble_eq_true, &[base, n, hh]);
                    let ble_le_m = d.lemma(p.le_trans, &[base, n, m, ble_le_n, hnm]);
                    d.lemma(p.ble_eq_true_of_le, &[base, m, ble_le_m])
                };
                let outer_result = le_of_bool_select_mono(
                    d,
                    &p,
                    base_fits_n,
                    base_fits_m,
                    inner_term_lhs,
                    inner_term_rhs,
                    &to_test2_true,
                    inner_result,
                );

                let with_hnm = d.lam_fv(hnm_fv, hnm_ty, outer_result);
                let with_hfg = d.lam_fv(hfg_fv, hfg_ty, with_hnm);
                let with_m = d.lam_fv(m_fv, nat, with_hfg);
                d.lam_fv(n_fv, nat, with_m)
            };

            let g_fv = d.fresh_fvar();
            let g = d.kernel().fvar(g_fv);
            let per_g_result =
                super::ops::cases_zero_succ(d, g, &per_g_motive, &at_g_zero, &at_g_succ);
            d.lam_fv(g_fv, nat, per_g_result)
        };

        let proof = d.induct(&motive_at, &base_case, &step_case, f);
        let stmt = motive_at(d, f);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Nat.log_mono_right : ∀ b n m, Le n m → Le (log b n) (log b m)`.
pub(super) fn declare_log_mono_right(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.log_mono_right, 3, &|d, values| {
        let (base, n, m) = (values[0], values[1], values[2]);
        let h_ty = d.le(n, m);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let proof_body = d.lemma(p.log_aux_mono, &[base, n, m, n, m, h, h]);
        let log_n = log(d, &p, base, n);
        let log_m = log(d, &p, base, m);
        let concl = d.le(log_n, log_m);
        let stmt = d.arrow(h_ty, concl);
        let proof = d.lam_fv(h_fv, h_ty, proof_body);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Nat.log_monotone : ∀ b, Monotone (log b)` — the core-rendered unfolding
/// (`Monotone f` is Mathlib's own `∀ x y, x ≤ y → f x ≤ f y`), the same
/// treatment already given `Nat.choose_mono`.
pub(super) fn declare_log_monotone(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.log_monotone, 3, &|d, values| {
        let (base, n, m) = (values[0], values[1], values[2]);
        let h_ty = d.le(n, m);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let proof_body = d.lemma(p.log_mono_right, &[base, n, m, h]);
        let log_n = log(d, &p, base, n);
        let log_m = log(d, &p, base, m);
        let concl = d.le(log_n, log_m);
        let stmt = d.arrow(h_ty, concl);
        let proof = d.lam_fv(h_fv, h_ty, proof_body);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Nat.clog_aux_mono : ∀ b f g n m, Le f g → Le n m → Le (clogAux b f n)
/// (clogAux b g m)` — [`declare_log_aux_mono`]'s counterpart, with the
/// guard nesting swapped (`clog.rs`'s outer cut `2 ≤ b` is the SAME test
/// both sides; the inner cut `2 ≤ n`/`2 ≤ m` differs) and the recursive
/// argument's monotonicity coming from `add_le_add_right` + `pred_le_pred`
/// (`sub x 1` is definitionally `pred x`) then
/// [`declare_div_le_div_right`].
pub(super) fn declare_clog_aux_mono(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    d.theorem(p.clog_aux_mono, 2, &|d, values| {
        let (base, f) = (values[0], values[1]);
        let two = d.num(2);
        let base_exceeds_one = d.ble(two, base);

        let motive_at = move |d: &mut NatDev<'_>, fc: ExprId| -> ExprId {
            let g_fv = d.fresh_fvar();
            let g = d.kernel().fvar(g_fv);
            let n_fv = d.fresh_fvar();
            let n = d.kernel().fvar(n_fv);
            let m_fv = d.fresh_fvar();
            let m = d.kernel().fvar(m_fv);
            let hfg_ty = d.le(fc, g);
            let hnm_ty = d.le(n, m);
            let lhs = clog_aux(d, &p, base, fc, n);
            let rhs = clog_aux(d, &p, base, g, m);
            let concl = d.le(lhs, rhs);
            let with_hnm = d.arrow(hnm_ty, concl);
            let with_hfg = d.arrow(hfg_ty, with_hnm);
            let with_m = d.pi_fv(m_fv, nat, with_hfg);
            let with_n = d.pi_fv(n_fv, nat, with_m);
            d.pi_fv(g_fv, nat, with_n)
        };

        let base_case = move |d: &mut NatDev<'_>| -> ExprId {
            let g_fv = d.fresh_fvar();
            let g = d.kernel().fvar(g_fv);
            let n_fv = d.fresh_fvar();
            let m_fv = d.fresh_fvar();
            let m = d.kernel().fvar(m_fv);
            let zero = d.zero();
            let hfg_ty = d.le(zero, g);
            let n_stub = d.kernel().fvar(n_fv);
            let hnm_ty = d.le(n_stub, m);
            let hfg_fv = d.fresh_fvar();
            let hnm_fv = d.fresh_fvar();
            let rhs = clog_aux(d, &p, base, g, m);
            let proof_body = d.lemma(p.zero_le, &[rhs]);
            let with_hnm = d.lam_fv(hnm_fv, hnm_ty, proof_body);
            let with_hfg = d.lam_fv(hfg_fv, hfg_ty, with_hnm);
            let with_m = d.lam_fv(m_fv, nat, with_hfg);
            let with_n = d.lam_fv(n_fv, nat, with_m);
            d.lam_fv(g_fv, nat, with_n)
        };

        let step_case = move |d: &mut NatDev<'_>, predecessor: ExprId, ih: ExprId| -> ExprId {
            let succ_f = d.succ(predecessor);

            let per_g_motive = move |d: &mut NatDev<'_>, gc: ExprId| -> ExprId {
                let n_fv = d.fresh_fvar();
                let n = d.kernel().fvar(n_fv);
                let m_fv = d.fresh_fvar();
                let m = d.kernel().fvar(m_fv);
                let hfg_ty = d.le(succ_f, gc);
                let hnm_ty = d.le(n, m);
                let lhs = clog_aux(d, &p, base, succ_f, n);
                let rhs = clog_aux(d, &p, base, gc, m);
                let concl = d.le(lhs, rhs);
                let with_hnm = d.arrow(hnm_ty, concl);
                let with_hfg = d.arrow(hfg_ty, with_hnm);
                let with_m = d.pi_fv(m_fv, nat, with_hfg);
                d.pi_fv(n_fv, nat, with_m)
            };

            let at_g_zero = move |d: &mut NatDev<'_>| -> ExprId {
                let n_fv = d.fresh_fvar();
                let n = d.kernel().fvar(n_fv);
                let m_fv = d.fresh_fvar();
                let m = d.kernel().fvar(m_fv);
                let zero = d.zero();
                let hfg_ty = d.le(succ_f, zero);
                let hnm_ty = d.le(n, m);
                let hfg_fv = d.fresh_fvar();
                let hfg = d.kernel().fvar(hfg_fv);
                let hnm_fv = d.fresh_fvar();
                let absurd = d.lemma(p.not_succ_le_zero, &[predecessor, hfg]);
                let lhs = clog_aux(d, &p, base, succ_f, n);
                let rhs = clog_aux(d, &p, base, zero, m);
                let target = d.le(lhs, rhs);
                let elim = false_elim(d, &p, target, absurd);
                let with_hnm = d.lam_fv(hnm_fv, hnm_ty, elim);
                let with_hfg = d.lam_fv(hfg_fv, hfg_ty, with_hnm);
                let with_m = d.lam_fv(m_fv, nat, with_hfg);
                d.lam_fv(n_fv, nat, with_m)
            };

            let at_g_succ = move |d: &mut NatDev<'_>, g_prime: ExprId| -> ExprId {
                let n_fv = d.fresh_fvar();
                let n = d.kernel().fvar(n_fv);
                let m_fv = d.fresh_fvar();
                let m = d.kernel().fvar(m_fv);
                let succ_g_prime = d.succ(g_prime);
                let hfg_ty = d.le(succ_f, succ_g_prime);
                let hnm_ty = d.le(n, m);
                let hfg_fv = d.fresh_fvar();
                let hfg = d.kernel().fvar(hfg_fv);
                let hnm_fv = d.fresh_fvar();
                let hnm = d.kernel().fvar(hnm_fv);

                let f_le_g_prime = d.lemma(p.le_of_succ_le_succ, &[predecessor, g_prime, hfg]);

                let one = d.num(1);
                let sum_n = d.add(n, base);
                let sum_m = d.add(m, base);
                let numerator_n = d.sub(sum_n, one);
                let numerator_m = d.sub(sum_m, one);
                let quotient_n = d.div(numerator_n, base);
                let quotient_m = d.div(numerator_m, base);

                let sum_le = d.lemma(p.add_le_add_right, &[base, n, m, hnm]);
                let pred_le = d.lemma(p.pred_le_pred, &[sum_n, sum_m, sum_le]);
                let hnm_div = d.lemma(
                    p.div_le_div_right,
                    &[numerator_n, numerator_m, base, pred_le],
                );

                let ih_at_g = d.apply(
                    ih,
                    &[g_prime, quotient_n, quotient_m, f_le_g_prime, hnm_div],
                );
                let inner_lhs = clog_aux(d, &p, base, predecessor, quotient_n);
                let inner_rhs = clog_aux(d, &p, base, g_prime, quotient_m);
                let stepped_lhs = d.succ(inner_lhs);
                let stepped_rhs = d.succ(inner_rhs);
                let proof_stepped_le = d.lemma(p.le_succ_succ, &[inner_lhs, inner_rhs, ih_at_g]);

                let value_exceeds_one_n = d.ble(two, n);
                let value_exceeds_one_m = d.ble(two, m);
                let to_test2_true = move |d: &mut NatDev<'_>, hh: ExprId| -> ExprId {
                    let ble_le_n = d.lemma(p.le_of_ble_eq_true, &[two, n, hh]);
                    let ble_le_m = d.lemma(p.le_trans, &[two, n, m, ble_le_n, hnm]);
                    d.lemma(p.ble_eq_true_of_le, &[two, m, ble_le_m])
                };
                let inner_result = le_of_bool_select_mono(
                    d,
                    &p,
                    value_exceeds_one_n,
                    value_exceeds_one_m,
                    stepped_lhs,
                    stepped_rhs,
                    &to_test2_true,
                    proof_stepped_le,
                );

                let zero = d.zero();
                let inner_term_lhs = d.bool_select_nat(value_exceeds_one_n, stepped_lhs, zero);
                let inner_term_rhs = d.bool_select_nat(value_exceeds_one_m, stepped_rhs, zero);
                let outer_result = le_of_bool_select_mono(
                    d,
                    &p,
                    base_exceeds_one,
                    base_exceeds_one,
                    inner_term_lhs,
                    inner_term_rhs,
                    &|_d, h2| h2,
                    inner_result,
                );

                let with_hnm = d.lam_fv(hnm_fv, hnm_ty, outer_result);
                let with_hfg = d.lam_fv(hfg_fv, hfg_ty, with_hnm);
                let with_m = d.lam_fv(m_fv, nat, with_hfg);
                d.lam_fv(n_fv, nat, with_m)
            };

            let g_fv = d.fresh_fvar();
            let g = d.kernel().fvar(g_fv);
            let per_g_result =
                super::ops::cases_zero_succ(d, g, &per_g_motive, &at_g_zero, &at_g_succ);
            d.lam_fv(g_fv, nat, per_g_result)
        };

        let proof = d.induct(&motive_at, &base_case, &step_case, f);
        let stmt = motive_at(d, f);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Nat.clog_mono_right : ∀ b n m, Le n m → Le (clog b n) (clog b m)`.
pub(super) fn declare_clog_mono_right(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.clog_mono_right, 3, &|d, values| {
        let (base, n, m) = (values[0], values[1], values[2]);
        let h_ty = d.le(n, m);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let proof_body = d.lemma(p.clog_aux_mono, &[base, n, m, n, m, h, h]);
        let clog_n = clog(d, &p, base, n);
        let clog_m = clog(d, &p, base, m);
        let concl = d.le(clog_n, clog_m);
        let stmt = d.arrow(h_ty, concl);
        let proof = d.lam_fv(h_fv, h_ty, proof_body);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Nat.clog_monotone : ∀ b, Monotone (clog b)` — the same core-rendered
/// unfolding as [`declare_log_monotone`].
pub(super) fn declare_clog_monotone(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.clog_monotone, 3, &|d, values| {
        let (base, n, m) = (values[0], values[1], values[2]);
        let h_ty = d.le(n, m);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let proof_body = d.lemma(p.clog_mono_right, &[base, n, m, h]);
        let clog_n = clog(d, &p, base, n);
        let clog_m = clog(d, &p, base, m);
        let concl = d.le(clog_n, clog_m);
        let stmt = d.arrow(h_ty, concl);
        let proof = d.lam_fv(h_fv, h_ty, proof_body);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Nat.clog_pos : ∀ b n, Lt 1 b → Lt 1 n → Lt 0 (clog b n)`.
///
/// Case-split on `n` (`clog`'s fuel and value are diagonal, so this single
/// split gives both the succ-shaped fuel the unfolding needs and the
/// succ-shaped value the guard needs); `n = 0` is refuted by `Lt 1 0`
/// (`Le 2 0`) via `not_succ_le_zero`. At `n = succ n'` both guard cuts are
/// already known true from the hypotheses (no case split needed — direct
/// `bool_transport` at the known evidence), so `clog b n` reduces to a
/// `succ`, positive by `zero_lt_succ`.
pub(super) fn declare_clog_pos(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.clog_pos, 2, &|d, values| {
        let (base, n) = (values[0], values[1]);
        let one = d.num(1);
        let h1_ty = d.lt(one, base);
        let h2_ty = d.lt(one, n);
        let h1_fv = d.fresh_fvar();
        let h1 = d.kernel().fvar(h1_fv);

        let motive_at = move |d: &mut NatDev<'_>, nc: ExprId| -> ExprId {
            let h2_ty = d.lt(one, nc);
            let zero = d.zero();
            let cl = clog(d, &p, base, nc);
            let concl = d.lt(zero, cl);
            d.arrow(h2_ty, concl)
        };

        let at_n_zero = move |d: &mut NatDev<'_>| -> ExprId {
            let zero = d.zero();
            let h2_ty = d.lt(one, zero);
            let h2_fv = d.fresh_fvar();
            let h2 = d.kernel().fvar(h2_fv);
            let absurd = d.lemma(p.not_succ_le_zero, &[one, h2]);
            let cl = clog(d, &p, base, zero);
            let target = d.lt(zero, cl);
            let elim = false_elim(d, &p, target, absurd);
            d.lam_fv(h2_fv, h2_ty, elim)
        };

        let at_n_succ = move |d: &mut NatDev<'_>, n_prime: ExprId| -> ExprId {
            let succ_n_prime = d.succ(n_prime);
            let h2_ty = d.lt(one, succ_n_prime);
            let h2_fv = d.fresh_fvar();
            let h2 = d.kernel().fvar(h2_fv);

            let two = d.num(2);
            let base_exceeds_one = d.ble(two, base);
            let value_exceeds_one = d.ble(two, succ_n_prime);
            let proof_b_true = d.lemma(p.ble_eq_true_of_le, &[two, base, h1]);
            let proof_n_true = d.lemma(p.ble_eq_true_of_le, &[two, succ_n_prime, h2]);

            let sum_arg = d.add(succ_n_prime, base);
            let one2 = d.num(1);
            let numerator = d.sub(sum_arg, one2);
            let quotient = d.div(numerator, base);
            let recursive = clog_aux(d, &p, base, n_prime, quotient);
            let stepped = d.succ(recursive);
            let zero = d.zero();

            // Transport `Lt 0 stepped` (via `zero_lt_succ`) along the KNOWN
            // `true` evidence, at each guard level in turn -- no case split
            // needed, since both guards' truth is already in hand.
            let true_ = d.bool_true();
            let pos = d.lemma(p.zero_lt_succ, &[recursive]);

            let inner_term = d.bool_select_nat(value_exceeds_one, stepped, zero);
            let motive_inner = d.bool_eq_motive(true_, &|d, x| {
                let selected = d.bool_select_nat(x, stepped, zero);
                d.lt(zero, selected)
            });
            let reversed_n = d.bool_symm(value_exceeds_one, true_, proof_n_true);
            let pos_inner =
                d.bool_transport(true_, motive_inner, pos, value_exceeds_one, reversed_n);

            let motive_outer = d.bool_eq_motive(true_, &move |d, x| {
                let selected = d.bool_select_nat(x, inner_term, zero);
                d.lt(zero, selected)
            });
            let reversed_b = d.bool_symm(base_exceeds_one, true_, proof_b_true);
            let pos_outer =
                d.bool_transport(true_, motive_outer, pos_inner, base_exceeds_one, reversed_b);
            d.lam_fv(h2_fv, h2_ty, pos_outer)
        };

        let body = super::ops::cases_zero_succ(d, n, &motive_at, &at_n_zero, &at_n_succ);
        let zero = d.zero();
        let cl = clog(d, &p, base, n);
        let final_concl = d.lt(zero, cl);
        let inner_arrow = d.arrow(h2_ty, final_concl);
        let stmt = d.arrow(h1_ty, inner_arrow);
        let proof = d.lam_fv(h1_fv, h1_ty, body);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Le n (sub (add n base) 1)`, given `h_one_le_base : Le 1 base` — i.e. `n ≤
/// n+base-1`. `pred_le_pred(add_le_add_left(n, 1, base, h_one_le_base))` has
/// type `Le (pred (add n 1)) (pred (add n base))`, which is DEFEQ to the
/// stated `Le n (sub (add n base) 1)`: `add n 1 ≡ succ n` (`Nat.add`'s
/// zero-case for the right operand, one iota step past `add n (succ zero)`),
/// `pred (succ n) ≡ n` (iota), and `sub x 1 ≡ pred x` (two iota steps through
/// `Nat.sub`'s structural definition, as `clog.rs`'s module doc notes).
fn n_le_add_sub_one(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    n: ExprId,
    base: ExprId,
    h_one_le_base: ExprId,
) -> ExprId {
    let p = *p;
    let one = d.num(1);
    let add_le = d.lemma(p.add_le_add_left, &[n, one, base, h_one_le_base]);
    let n_plus_one = d.add(n, one);
    let n_plus_base = d.add(n, base);
    d.lemma(p.pred_le_pred, &[n_plus_one, n_plus_base, add_le])
}

/// `Nat.log_aux_le_clog_aux : ∀ b f n, Le (logAux b f n) (clogAux b f n)`.
/// See the module doc / `NatPrelude::log_aux_le_clog_aux`'s doc comment for
/// the route.
pub(super) fn declare_log_aux_le_clog_aux(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    d.theorem(p.log_aux_le_clog_aux, 2, &|d, values| {
        let (base, f) = (values[0], values[1]);
        let two = d.num(2);
        let base_exceeds_one = d.ble(two, base);
        let true_ = d.bool_true();
        let false_ = d.bool_false();
        let zero = d.zero();

        let motive_at = move |d: &mut NatDev<'_>, fc: ExprId| -> ExprId {
            let n_fv = d.fresh_fvar();
            let n = d.kernel().fvar(n_fv);
            let lhs = log_aux(d, &p, base, fc, n);
            let rhs = clog_aux(d, &p, base, fc, n);
            let body = d.le(lhs, rhs);
            d.pi_fv(n_fv, nat, body)
        };

        let base_case = move |d: &mut NatDev<'_>| -> ExprId {
            let n_fv = d.fresh_fvar();
            let zero = d.zero();
            let proof = d.lemma(p.le_refl, &[zero]);
            d.lam_fv(n_fv, nat, proof)
        };

        let step_case = move |d: &mut NatDev<'_>, predecessor: ExprId, ih: ExprId| -> ExprId {
            let n_fv = d.fresh_fvar();
            let n = d.kernel().fvar(n_fv);
            let succ_f = d.succ(predecessor);

            let base_fits = d.ble(base, n);
            let value_exceeds_one = d.ble(two, n);
            let one = d.num(1);

            let quotient_log = d.div(n, base);
            let inner_log_val = log_aux(d, &p, base, predecessor, quotient_log);
            let stepped_log = d.succ(inner_log_val);
            let inner_log_term = d.bool_select_nat(base_exceeds_one, stepped_log, zero);
            let lhs_full = d.bool_select_nat(base_fits, inner_log_term, zero);

            let sum_n = d.add(n, base);
            let numerator_n = d.sub(sum_n, one);
            let quotient_clog = d.div(numerator_n, base);
            let inner_clog_val = clog_aux(d, &p, base, predecessor, quotient_clog);
            let stepped_clog = d.succ(inner_clog_val);
            let inner_clog_term = d.bool_select_nat(value_exceeds_one, stepped_clog, zero);
            let rhs_full = d.bool_select_nat(base_exceeds_one, inner_clog_term, zero);

            let lhs_ctor = log_aux(d, &p, base, succ_f, n);
            let rhs_ctor = clog_aux(d, &p, base, succ_f, n);
            let goal = d.le(lhs_ctor, rhs_ctor);

            let is_true1 = d.bool_eq(base_exceeds_one, true_);
            let is_false1 = d.bool_eq(base_exceeds_one, false_);

            // base_exceeds_one = false: both sides collapse to 0.
            let case_false1 = {
                let h1_fv = d.fresh_fvar();
                let h1 = d.kernel().fvar(h1_fv);

                // logAux's inner selector (same test) reduces to 0, then
                // `bool_select_nat_same` collapses the outer `base_fits`
                // selector regardless of its value.
                let motive_inner = d.bool_eq_motive(false_, &|d, x| {
                    let selected = d.bool_select_nat(x, stepped_log, zero);
                    d.eq(selected, zero)
                });
                let refl_inner = d.refl(zero);
                let reversed1a = d.bool_symm(base_exceeds_one, false_, h1);
                let inner_eq_zero = d.bool_transport(
                    false_,
                    motive_inner,
                    refl_inner,
                    base_exceeds_one,
                    reversed1a,
                );
                let mid = d.bool_select_nat(base_fits, zero, zero);
                let congr_step = d.congr(inner_log_term, zero, inner_eq_zero, &|d, x| {
                    d.bool_select_nat(base_fits, x, zero)
                });
                let same_step = super::ops::bool_select_nat_same(d, &p, base_fits, zero);
                let (_, lhs_eq_zero) = d.chain(lhs_full, &[(mid, congr_step), (zero, same_step)]);

                // clogAux's outer selector is the SAME false test.
                let motive_outer = d.bool_eq_motive(false_, &|d, x| {
                    let selected = d.bool_select_nat(x, inner_clog_term, zero);
                    d.eq(selected, zero)
                });
                let refl_outer = d.refl(zero);
                let reversed1b = d.bool_symm(base_exceeds_one, false_, h1);
                let rhs_eq_zero = d.bool_transport(
                    false_,
                    motive_outer,
                    refl_outer,
                    base_exceeds_one,
                    reversed1b,
                );

                let le_zero_zero = d.lemma(p.le_refl, &[zero]);
                let motive_r = d.eq_motive(zero, &move |d, x| d.le(zero, x));
                let symm_rhs = d.symm(rhs_full, zero, rhs_eq_zero);
                let step1 = d.transport(zero, motive_r, le_zero_zero, rhs_full, symm_rhs);
                let motive_l = d.eq_motive(zero, &move |d, x| d.le(x, rhs_full));
                let symm_lhs = d.symm(lhs_full, zero, lhs_eq_zero);
                let proof = d.transport(zero, motive_l, step1, lhs_full, symm_lhs);
                d.lam_fv(h1_fv, is_false1, proof)
            };

            // base_exceeds_one = true.
            let case_true1 = {
                let h1_fv = d.fresh_fvar();
                let h1 = d.kernel().fvar(h1_fv);
                let hb1_le = d.lemma(p.le_of_ble_eq_true, &[two, base, h1]);

                let is_true2 = d.bool_eq(base_fits, true_);
                let is_false2 = d.bool_eq(base_fits, false_);

                // base_fits = false: lhs collapses to 0 regardless of rhs.
                let case_false2 = {
                    let h2_fv = d.fresh_fvar();
                    let h2 = d.kernel().fvar(h2_fv);
                    let zero_le_rhs = d.lemma(p.zero_le, &[rhs_full]);
                    let motive2 = d.bool_eq_motive(false_, &move |d, x| {
                        let selected = d.bool_select_nat(x, inner_log_term, zero);
                        d.le(selected, rhs_full)
                    });
                    let reversed2 = d.bool_symm(base_fits, false_, h2);
                    let proof =
                        d.bool_transport(false_, motive2, zero_le_rhs, base_fits, reversed2);
                    d.lam_fv(h2_fv, is_false2, proof)
                };

                // base_fits = true: the hard leaf.
                let case_true2 = {
                    let h2_fv = d.fresh_fvar();
                    let h2 = d.kernel().fvar(h2_fv);
                    let hbase_n_le = d.lemma(p.le_of_ble_eq_true, &[base, n, h2]);
                    let two_le_n = d.lemma(p.le_trans, &[two, base, n, hb1_le, hbase_n_le]);
                    let value_exceeds_one_true = d.lemma(p.ble_eq_true_of_le, &[two, n, two_le_n]);

                    let le_one_two = d.lemma(p.le_succ, &[one]);
                    let le_one_base = d.lemma(p.le_trans, &[one, two, base, le_one_two, hb1_le]);
                    let n_le_numerator = n_le_add_sub_one(d, &p, n, base, le_one_base);
                    let div_mono =
                        d.lemma(p.div_le_div_right, &[n, numerator_n, base, n_le_numerator]);

                    let ih_at_qlog = d.apply(ih, &[quotient_log]);
                    let pred_refl = d.lemma(p.le_refl, &[predecessor]);
                    let clog_mono_at_qlog = d.lemma(
                        p.clog_aux_mono,
                        &[
                            base,
                            predecessor,
                            predecessor,
                            quotient_log,
                            quotient_clog,
                            pred_refl,
                            div_mono,
                        ],
                    );
                    let clog_ql = clog_aux(d, &p, base, predecessor, quotient_log);
                    let clog_qc = clog_aux(d, &p, base, predecessor, quotient_clog);
                    let chained = d.lemma(
                        p.le_trans,
                        &[
                            inner_log_val,
                            clog_ql,
                            clog_qc,
                            ih_at_qlog,
                            clog_mono_at_qlog,
                        ],
                    );
                    let main_le = d.lemma(p.le_succ_succ, &[inner_log_val, clog_qc, chained]);

                    // Lift `main_le : Le stepped_log stepped_clog` through
                    // both aux families' bool_selects (inner then outer,
                    // per side).
                    let value_exceeds_one_true_rev =
                        d.bool_symm(value_exceeds_one, true_, value_exceeds_one_true);
                    let motive_r1 = d.bool_eq_motive(true_, &move |d, x| {
                        let sel = d.bool_select_nat(x, stepped_clog, zero);
                        d.le(stepped_log, sel)
                    });
                    let step_r1 = d.bool_transport(
                        true_,
                        motive_r1,
                        main_le,
                        value_exceeds_one,
                        value_exceeds_one_true_rev,
                    );

                    let h1_rev = d.bool_symm(base_exceeds_one, true_, h1);
                    let motive_r2 = d.bool_eq_motive(true_, &move |d, x| {
                        let sel = d.bool_select_nat(x, inner_clog_term, zero);
                        d.le(stepped_log, sel)
                    });
                    let step_r2 =
                        d.bool_transport(true_, motive_r2, step_r1, base_exceeds_one, h1_rev);

                    let h1_rev2 = d.bool_symm(base_exceeds_one, true_, h1);
                    let motive_l1 = d.bool_eq_motive(true_, &move |d, x| {
                        let sel = d.bool_select_nat(x, stepped_log, zero);
                        d.le(sel, rhs_full)
                    });
                    let step_l1 =
                        d.bool_transport(true_, motive_l1, step_r2, base_exceeds_one, h1_rev2);

                    let h2_rev = d.bool_symm(base_fits, true_, h2);
                    let motive_l2 = d.bool_eq_motive(true_, &move |d, x| {
                        let sel = d.bool_select_nat(x, inner_log_term, zero);
                        d.le(sel, rhs_full)
                    });
                    let proof = d.bool_transport(true_, motive_l2, step_l1, base_fits, h2_rev);
                    d.lam_fv(h2_fv, is_true2, proof)
                };

                let split2 = super::ops::bool_true_or_false(d, &p, base_fits);
                let inner_proof = or_cases(
                    d,
                    &p,
                    is_true2,
                    is_false2,
                    goal,
                    case_true2,
                    case_false2,
                    split2,
                );
                d.lam_fv(h1_fv, is_true1, inner_proof)
            };

            let split1 = super::ops::bool_true_or_false(d, &p, base_exceeds_one);
            let full_proof = or_cases(
                d,
                &p,
                is_true1,
                is_false1,
                goal,
                case_true1,
                case_false1,
                split1,
            );
            d.lam_fv(n_fv, nat, full_proof)
        };

        let proof = d.induct(&motive_at, &base_case, &step_case, f);
        let stmt = motive_at(d, f);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Nat.log_le_clog : ∀ b n, Le (log b n) (clog b n)` —
/// [`declare_log_aux_le_clog_aux`] at the diagonal `f := n`.
pub(super) fn declare_log_le_clog(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.log_le_clog, 2, &|d, values| {
        let (base, n) = (values[0], values[1]);
        let proof = d.lemma(p.log_aux_le_clog_aux, &[base, n, n]);
        let log_n = log(d, &p, base, n);
        let clog_n = clog(d, &p, base, n);
        let stmt = d.le(log_n, clog_n);
        (stmt, proof)
    })?;
    Ok(())
}

/// Declare every `log`/`clog` order mirror this file carries.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_log_clog_order_all(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    declare_div_le_div_right(d, p)?;
    declare_log_aux_mono(d, p)?;
    declare_log_mono_right(d, p)?;
    declare_log_monotone(d, p)?;
    declare_clog_aux_mono(d, p)?;
    declare_clog_mono_right(d, p)?;
    declare_clog_monotone(d, p)?;
    declare_clog_pos(d, p)?;
    declare_log_aux_le_clog_aux(d, p)?;
    declare_log_le_clog(d, p)?;
    Ok(())
}
