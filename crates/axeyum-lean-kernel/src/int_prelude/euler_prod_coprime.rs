//! `Int.prodRangeIf_coprime : ∀ pred f n m, 0 < m →
//! (∀ k, Lt k n → Eq Bool (pred k) true → Coprime (f k) m) →
//! Coprime (prodRange (selector pred f) n) m` — a restricted product of
//! `m`-coprime factors stays coprime to `m`. Part of item 3 of the
//! Fermat -> Euler handoff (`docs/plan/status/374-euler-theorem.md`,
//! `euler_theorem.rs`'s module doc): the ingredient
//! `Int.modEq_cancel`/`Int.ModEq.cancel` needs before it can cancel
//! `prodRangeIf pred (fun k => ofNat k) n` from both sides of the final
//! `ModEq`.
//!
//! ## Proof: induction on `n`, following `euler_prod_pow.rs`'s pattern
//!
//! Base (`n = 0`): `prodRange sel 0 ≡ one` by iota, and
//! [`super::euler_totient::coprime_one`] gives `Coprime one m`
//! unconditionally.
//!
//! Step (`n -> succ n`): weaken the `succ n`-bounded hypothesis to an
//! `n`-bounded one (the `Nat.le_succ` + `Nat.lt_of_lt_of_le` idiom
//! `prod.rs::declare_modeq_prod_range_lt` already uses) to get the
//! induction hypothesis `Coprime (prodRange sel n) m`, then decide
//! `Coprime (bool_select_int (pred n) (f n) one) m` by a genuine case split
//! on `pred n` (`euler_totient::bool_select_int_congr_cond`'s "generalize
//! the equation, apply `Bool.rec`" trick, [`bool_case_int`] below — NOT the
//! "supply the goal at each literal constructor" idiom `euler_prod_pow.rs`
//! uses, because THIS goal genuinely needs the hypothesis `pred n = true` to
//! invoke `h` at `n`, not merely a computational fact independent of it):
//!
//! - `pred n = true`: the hypothesis at `k := n` (`n < succ n` via
//!   `Nat.lt_succ_self`, plus the case's own `heq : pred n = true`) gives
//!   `Coprime (f n) m` directly; `bool_select_int_congr_cond` rewrites
//!   `bool_select_int (pred n) (f n) one` to `bool_select_int true (f n) one`
//!   (defeq `f n`), transporting the coprimality across.
//! - `pred n = false`: `bool_select_int (pred n) (f n) one` rewrites to
//!   `bool_select_int false (f n) one` (defeq `one`); `coprime_one` closes it,
//!   transported the same way.
//!
//! [`super::euler_totient::coprime_mul`] combines the induction hypothesis
//! with this per-element fact: `Coprime (mul (prodRange sel n) (sel n)) m`,
//! which is exactly `Coprime (prodRange sel (succ n)) m` by iota
//! (`prodRange_succ`'s defining equation).

use super::euler_theorem::bool_select_int_congr_cond;
use super::euler_totient::{coprime_mul, coprime_one};
use super::ops::IntDev;
use super::prod::bool_select_int;
use crate::KernelError;
use crate::expr::ExprId;
use crate::nat_prelude::NatOps;

/// `fun i => bool_select_int (pred i) (f i) Int.one` — a per-file local copy
/// of `euler_theorem.rs`'s private `selector` (this development's own
/// convention, per-file local copies over a shared private module — see
/// `nat_prelude/euler.rs`/`int_prelude/modinv.rs`'s doc comments on the same
/// choice).
fn selector(d: &mut IntDev<'_>, pred: ExprId, f: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let pi = d.apply(pred, &[i]);
    let fi = d.apply(f, &[i]);
    let one = d.ione();
    let sel = bool_select_int(d, pi, fi, one);
    d.lam_fv(i_fv, nat, sel)
}

/// Case-split on `cond : Bool` for a FIXED `goal`, with `heq : Eq Bool cond
/// true`/`Eq Bool cond false` available inside the matching branch — a local
/// IntDev-typed copy of `nat_prelude/subset_product.rs`'s private `bool_case`
/// (the "generalize the selector, then instantiate at `bool_refl(condition)`"
/// trick; that file's own doc traces it to `finite.rs::compact_eq_of_gt`).
/// Needed here (rather than the simpler "supply the goal at each literal
/// constructor" idiom) because both branches genuinely need the equation
/// `heq` as a real hypothesis, not merely a computational fact.
fn bool_case_int(
    d: &mut IntDev<'_>,
    cond: ExprId,
    goal: ExprId,
    case_true: &dyn Fn(&mut IntDev<'_>, ExprId) -> ExprId,
    case_false: &dyn Fn(&mut IntDev<'_>, ExprId) -> ExprId,
) -> ExprId {
    let p = d.int();
    let bool_ty = d.bool_ty();
    let true_val = d.bool_true();
    let false_val = d.bool_false();

    let false_minor = {
        let heq_fv = d.fresh_fvar();
        let heq_ty = d.bool_eq(cond, false_val);
        let heq = d.kernel().fvar(heq_fv);
        let body = case_false(d, heq);
        d.lam_fv(heq_fv, heq_ty, body)
    };
    let true_minor = {
        let heq_fv = d.fresh_fvar();
        let heq_ty = d.bool_eq(cond, true_val);
        let heq = d.kernel().fvar(heq_fv);
        let body = case_true(d, heq);
        d.lam_fv(heq_fv, heq_ty, body)
    };
    let motive = {
        let sel_fv = d.fresh_fvar();
        let sel = d.kernel().fvar(sel_fv);
        let eq_cond_sel = d.bool_eq(cond, sel);
        let body = d.arrow(eq_cond_sel, goal);
        d.lam_fv(sel_fv, bool_ty, body)
    };
    let level_zero = d.kernel().level_zero();
    let bool_rec = d.kernel().const_(p.logic.bool_rec, vec![level_zero]);
    let selected = d.apply(bool_rec, &[motive, false_minor, true_minor, cond]);
    let cond_refl = d.bool_refl(cond);
    d.apply(selected, &[cond_refl])
}

/// Declare `Int.prodRangeIf_coprime : ∀ pred f n m, 0 < m →
/// (∀ k, Lt k n → Eq Bool (pred k) true → Coprime (f k) m) →
/// Eq Int … → Coprime (prodRange (selector pred f) n) m` (see the module
/// doc for the full statement, built in `prodRange`/`selector`-unfolded
/// form matching `euler_theorem.rs`'s and `euler_prod_pow.rs`'s own
/// convention).
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
#[allow(clippy::too_many_lines)]
pub(super) fn declare_prod_range_if_coprime(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    let nat = d.nat_ty();
    let bool_ty = d.bool_ty();
    let int_ty = d.int_ty();
    let pred_ty = d.arrow(nat, bool_ty);
    let fn_ty = d.arrow(nat, int_ty);
    let true_v = d.bool_true();

    let pred_fv = d.fresh_fvar();
    let pred = d.kernel().fvar(pred_fv);
    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);

    let zero_i = d.izero();
    let pos_ty = d.ilt(zero_i, m);

    // `bounded_pointwise(bound) := ∀ k, Lt k bound → Eq Bool (pred k) true →
    // Coprime (f k) m`.
    let bounded_pointwise = |d: &mut IntDev<'_>, bound: ExprId| -> ExprId {
        let p = d.int();
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let hk_ty = d.lt(k, bound);
        let pk = d.apply(pred, &[k]);
        let pk_true_ty = d.bool_eq(pk, true_v);
        let fk = d.apply(f, &[k]);
        let cop_ty = d.const_app(p.coprime, &[fk, m]);
        let inner = d.arrow(pk_true_ty, cop_ty);
        let with_hk = d.arrow(hk_ty, inner);
        d.pi_fv(k_fv, nat, with_hk)
    };

    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let p = d.int();
        let hyp = bounded_pointwise(d, x);
        let sel = selector(d, pred, f);
        let pr = d.const_app(p.prod_range, &[sel, x]);
        let concl = d.const_app(p.coprime, &[pr, m]);
        d.arrow(hyp, concl)
    };
    let stmt_at_n = motive(d, n);

    let h_pos_fv = d.fresh_fvar();
    let h_pos = d.kernel().fvar(h_pos_fv);

    let proof_body = d.induct(
        &motive,
        &|d| {
            let zero_n = d.zero();
            let hyp_ty = bounded_pointwise(d, zero_n);
            let h_fv = d.fresh_fvar();
            let body = coprime_one(d, m);
            d.lam_fv(h_fv, hyp_ty, body)
        },
        &|d, j, ih| {
            let p = d.int();
            let sj = d.succ(j);
            let hyp_ty = bounded_pointwise(d, sj);
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);

            // Weaken `h : hyp(succ j)` to `hyp(j)`, for the induction
            // hypothesis.
            let h_lt_j = {
                let k_fv = d.fresh_fvar();
                let k = d.kernel().fvar(k_fv);
                let hk_ty = d.lt(k, j);
                let hk_fv = d.fresh_fvar();
                let hk = d.kernel().fvar(hk_fv);
                let pk_fv = d.fresh_fvar();
                let pk = d.kernel().fvar(pk_fv);
                let pk_ty = {
                    let pkk = d.apply(pred, &[k]);
                    d.bool_eq(pkk, true_v)
                };
                let le_succ_j = d.lemma(p.nat.le_succ, &[j]);
                let lifted = d.lemma(p.nat.lt_of_lt_of_le, &[k, j, sj, hk, le_succ_j]);
                let applied = d.apply(h, &[k, lifted, pk]);
                let with_pk = d.lam_fv(pk_fv, pk_ty, applied);
                let with_hk = d.lam_fv(hk_fv, hk_ty, with_pk);
                d.lam_fv(k_fv, nat, with_hk)
            };
            let ih_at_j = d.apply(ih, &[h_lt_j]);
            // ih_at_j : Coprime (prodRange sel j) m.

            let sel = selector(d, pred, f);
            let pr_j = d.const_app(p.prod_range, &[sel, j]);
            let pj = d.apply(pred, &[j]);
            let fj = d.apply(f, &[j]);
            let one_i = d.ione();
            let sel_j = bool_select_int(d, pj, fj, one_i);

            let sel_j_goal = {
                let p = d.int();
                d.const_app(p.coprime, &[sel_j, m])
            };
            let cop_sel_j = bool_case_int(
                d,
                pj,
                sel_j_goal,
                &|d, hpj_true| {
                    let p = d.int();
                    let lt_j_sj = d.lemma(p.nat.lt_succ_self, &[j]);
                    let cop_fj = d.apply(h, &[j, lt_j_sj, hpj_true]);
                    let true_v2 = d.bool_true();
                    let cong = bool_select_int_congr_cond(d, pj, true_v2, hpj_true, fj, one_i);
                    // cong : Eq Int sel_j (bool_select_int true fj one) --
                    // the RHS is defeq `fj`, so `cong` already has type
                    // `Eq Int sel_j fj`.
                    let fj_eq_sel_j = d.isymm(sel_j, fj, cong);
                    d.int_eq_rewrite(fj, sel_j, fj_eq_sel_j, cop_fj, &|d, t| {
                        let p = d.int();
                        d.const_app(p.coprime, &[t, m])
                    })
                },
                &|d, hpj_false| {
                    let false_v2 = d.bool_false();
                    let cong = bool_select_int_congr_cond(d, pj, false_v2, hpj_false, fj, one_i);
                    // cong : Eq Int sel_j (bool_select_int false fj one) --
                    // the RHS is defeq `one`, so `cong` already has type
                    // `Eq Int sel_j one`.
                    let cop_one = coprime_one(d, m);
                    let one_eq_sel_j = d.isymm(sel_j, one_i, cong);
                    d.int_eq_rewrite(one_i, sel_j, one_eq_sel_j, cop_one, &|d, t| {
                        let p = d.int();
                        d.const_app(p.coprime, &[t, m])
                    })
                },
            );

            let combined = coprime_mul(d, m, pr_j, sel_j, h_pos, ih_at_j, cop_sel_j);
            // combined : Coprime (mul pr_j sel_j) m, defeq
            // `Coprime (prodRange sel (succ j)) m` via `prodRange_succ`.

            d.lam_fv(h_fv, hyp_ty, combined)
        },
        n,
    );

    let with_h_pos = d.lam_fv(h_pos_fv, pos_ty, proof_body);

    let value = {
        let with_n = d.lam_fv(n_fv, nat, with_h_pos);
        let with_m = d.lam_fv(m_fv, int_ty, with_n);
        let with_f = d.lam_fv(f_fv, fn_ty, with_m);
        d.lam_fv(pred_fv, pred_ty, with_f)
    };
    let ty = {
        let inner = d.arrow(pos_ty, stmt_at_n);
        let with_n = d.pi_fv(n_fv, nat, inner);
        let with_m = d.pi_fv(m_fv, int_ty, with_n);
        let with_f = d.pi_fv(f_fv, fn_ty, with_m);
        d.pi_fv(pred_fv, pred_ty, with_f)
    };
    d.declare_theorem(p.prod_range_if_coprime, ty, value)
}
