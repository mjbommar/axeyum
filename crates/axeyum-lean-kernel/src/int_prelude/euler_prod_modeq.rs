//! `Int.prodRangeIf_modeq : ∀ n pred f g m, 0 < n →
//! (∀ k, ModEq n (f k) (g k)) →
//! ModEq n (prodRange (selector pred f) m) (prodRange (selector pred g) m)`
//! — a restricted product reduces mod `n` factor by factor, the termwise
//! `ModEq` transport step of item 3 of the Fermat -> Euler handoff
//! (`docs/plan/status/374-euler-theorem.md`, `euler_theorem.rs`'s module
//! doc): moves `prodRangeIf pred (fun k => emod (a*ofNat k) n) range` back
//! to `prodRangeIf pred (fun k => a*ofNat k) range` modulo `n`, via
//! `Int.euler_unit_coprime_iff`'s residue and
//! [`super::wilson::emod_modeq_self`].
//!
//! ## Proof: NOT a fresh induction, either
//!
//! Like `euler_prod_factor.rs`, this needs no induction of its own — the
//! hypothesis `h : ∀ k, ModEq n (f k) (g k)` is UNCONDITIONAL in `k` (it
//! does not depend on `pred k`), so the per-element selector-level `ModEq`
//! `ModEq n (bool_select_int (pred k) (f k) one) (bool_select_int (pred k)
//! (g k) one)` is closed by the same "supply the goal at each literal
//! constructor" idiom `euler_prod_factor.rs` uses (NOT
//! `euler_prod_coprime.rs`'s hypothesis-carrying case split, because neither
//! branch here needs `pred k`'s truth as a real premise — `h k` already
//! holds regardless):
//!
//! - `pred k = true`: `bool_select_int true (f k) one`/`… (g k) one` reduce
//!   (iota) to `f k`/`g k` — the goal IS `h k`, no lemma needed beyond
//!   supplying it.
//! - `pred k = false`: both reduce to `one` — `Int.ModEq.refl n one`.
//!
//! That pointwise selector-level `ModEq` feeds `Int.modEq_prodRange`
//! (unrestricted, already proved, `prod.rs`) directly — no new induction
//! anywhere in this file.

use super::modeq::imodeq;
use super::ops::IntDev;
use super::prod::bool_select_int;
use crate::KernelError;
use crate::expr::ExprId;
use crate::nat_prelude::NatOps;

/// `fun i => bool_select_int (pred i) (f i) Int.one` — a per-file local copy
/// of `euler_theorem.rs`'s private `selector` (this development's own
/// convention, per-file local copies over a shared private module).
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

/// Declare `Int.prodRangeIf_modeq` (see the module doc for the full
/// statement, built in `prodRange`/`selector`-unfolded form matching this
/// file's siblings' own convention).
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
#[allow(clippy::too_many_lines)]
pub(super) fn declare_prod_range_if_modeq(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    let nat = d.nat_ty();
    let bool_ty = d.bool_ty();
    let int_ty = d.int_ty();
    let pred_ty = d.arrow(nat, bool_ty);
    let fn_ty = d.arrow(nat, int_ty);

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let pred_fv = d.fresh_fvar();
    let pred = d.kernel().fvar(pred_fv);
    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);

    let zero_i = d.izero();
    let pos_ty = d.ilt(zero_i, n);

    let pointwise_ty = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let fk = d.apply(f, &[k]);
        let gk = d.apply(g, &[k]);
        let eqn = imodeq(d, n, fk, gk);
        d.pi_fv(k_fv, nat, eqn)
    };

    let sel_f = selector(d, pred, f);
    let sel_g = selector(d, pred, g);
    let prod_f_m = d.const_app(p.prod_range, &[sel_f, m]);
    let prod_g_m = d.const_app(p.prod_range, &[sel_g, m]);
    let concl = imodeq(d, n, prod_f_m, prod_g_m);

    let ty = {
        let inner = d.arrow(pointwise_ty, concl);
        let with_pos = d.arrow(pos_ty, inner);
        let with_m = d.pi_fv(m_fv, nat, with_pos);
        let with_g = d.pi_fv(g_fv, fn_ty, with_m);
        let with_f = d.pi_fv(f_fv, fn_ty, with_g);
        d.pi_fv(pred_fv, pred_ty, with_f)
    };
    let ty = d.pi_fv(n_fv, int_ty, ty);

    let h_pos_fv = d.fresh_fvar();
    let h_pos = d.kernel().fvar(h_pos_fv);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    // Pointwise, at the SELECTOR level: `forall k, ModEq n (sel_f k) (sel_g k)`.
    let sel_pointwise = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let pk = d.apply(pred, &[k]);
        let fk = d.apply(f, &[k]);
        let gk = d.apply(g, &[k]);
        let one_i = d.ione();
        let hk = d.apply(h, &[k]);
        // hk : ModEq n (f k) (g k)

        let motive_lam = {
            let x_fv = d.fresh_fvar();
            let x = d.kernel().fvar(x_fv);
            let selx_f = bool_select_int(d, x, fk, one_i);
            let selx_g = bool_select_int(d, x, gk, one_i);
            let body = imodeq(d, n, selx_f, selx_g);
            d.lam_fv(x_fv, bool_ty, body)
        };
        let case_true = hk;
        let case_false = d.const_app(p.mod_eq_refl, &[n, one_i]);
        let level_zero = d.kernel().level_zero();
        let bool_rec = d.int().logic.bool_rec;
        let rec = d.kernel().const_(bool_rec, vec![level_zero]);
        let body = d.apply(rec, &[motive_lam, case_false, case_true, pk]);
        d.lam_fv(k_fv, nat, body)
    };

    let proof_body = d.lemma(
        p.mod_eq_prod_range,
        &[n, sel_f, sel_g, m, h_pos, sel_pointwise],
    );

    let with_h = d.lam_fv(h_fv, pointwise_ty, proof_body);
    let with_h_pos = d.lam_fv(h_pos_fv, pos_ty, with_h);

    let value = {
        let with_m = d.lam_fv(m_fv, nat, with_h_pos);
        let with_g = d.lam_fv(g_fv, fn_ty, with_m);
        let with_f = d.lam_fv(f_fv, fn_ty, with_g);
        let with_pred = d.lam_fv(pred_fv, pred_ty, with_f);
        d.lam_fv(n_fv, int_ty, with_pred)
    };

    d.declare_theorem(p.prod_range_if_modeq, ty, value)
}
