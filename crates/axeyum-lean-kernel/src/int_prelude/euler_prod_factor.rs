//! `Int.prodRangeIf_factor_const_left : ∀ pred a f n,
//! Eq Int (prodRange (selector pred (fun k => a * f k)) n)
//!   (mul (prodRange (selector pred (fun _ => a)) n) (prodRange (selector pred f) n))`
//! — pointwise factoring of a constant `a` out of a restricted product, part
//! of item 3 of the Fermat -> Euler handoff
//! (`docs/plan/status/374-euler-theorem.md`, `euler_theorem.rs`'s module
//! doc): the step that turns `prodRangeIf pred (fun k => a * ofNat k) n`
//! (the product of shifted residues after `Int.euler_unit_coprime_iff`'s
//! `ModEq` transport) into `pow a (countRange pred n) * prodRangeIf pred
//! (fun k => ofNat k) n`.
//!
//! ## Proof: NOT a fresh induction
//!
//! The selector's payload identity `bool_select_int (pred i) (a * f i) one =
//! mul (bool_select_int (pred i) a one) (bool_select_int (pred i) f i one)`
//! holds unconditionally at every `i` — unlike `euler_prod_coprime.rs`'s case
//! split, neither branch needs `pred i`'s truth as a real hypothesis, so this
//! uses the SIMPLER "supply the goal at each literal constructor, apply
//! `Bool.rec` to the symbolic value" idiom (`euler_prod_pow.rs`'s own
//! pattern, traced there to `nat_prelude/totient.rs::count_step_le_one`):
//!
//! - `pred i = true`: both sides reduce (iota) to the identical term `mul a
//!   (f i)` — `Eq.refl`, no lemma.
//! - `pred i = false`: both sides reduce to `one`/`mul one one`; `Int.mul_one`
//!   (reversed) closes `Eq Int one (mul one one)`.
//!
//! That pointwise identity feeds `Int.prodRange_congr` (unrestricted, already
//! proved, `prod.rs`) to move from the `a * f` selector to the pointwise
//! `mul (selector … a) (selector … f)` one, and `Int.prodRange_mul`
//! (already proved, same file) finishes by pulling the product of two
//! `prodRange`s out of a `prodRange` of pointwise products. No new
//! induction anywhere in this file.

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

/// Declare `Int.prodRangeIf_factor_const_left` (see the module doc for the
/// full statement, built in `prodRange`/`selector`-unfolded form matching
/// `euler_theorem.rs`'s and `euler_prod_pow.rs`'s own convention).
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
#[allow(clippy::too_many_lines)]
pub(super) fn declare_prod_range_if_factor_const_left(
    d: &mut IntDev<'_>,
) -> Result<(), KernelError> {
    let p = d.int();
    let nat = d.nat_ty();
    let bool_ty = d.bool_ty();
    let int_ty = d.int_ty();
    let pred_ty = d.arrow(nat, bool_ty);
    let fn_ty = d.arrow(nat, int_ty);

    let pred_fv = d.fresh_fvar();
    let pred = d.kernel().fvar(pred_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    // `af := fun k => a * f k`.
    let af = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let fk = d.apply(f, &[k]);
        let body = d.imul(a, fk);
        d.lam_fv(k_fv, nat, body)
    };
    // `const_a := fun _ => a`.
    let const_a = {
        let unused_fv = d.fresh_fvar();
        d.lam_fv(unused_fv, nat, a)
    };

    let sel1 = selector(d, pred, af); // selector for `a * f`
    let sel_a = selector(d, pred, const_a); // selector for the constant `a`
    let sel_f = selector(d, pred, f); // selector for `f`

    let lhs = d.const_app(p.prod_range, &[sel1, n]);
    let rhs = {
        let pa = d.const_app(p.prod_range, &[sel_a, n]);
        let pf = d.const_app(p.prod_range, &[sel_f, n]);
        d.imul(pa, pf)
    };
    let concl = d.ieq(lhs, rhs);

    let ty = {
        let with_n = d.pi_fv(n_fv, nat, concl);
        let with_f = d.pi_fv(f_fv, fn_ty, with_n);
        let with_a = d.pi_fv(a_fv, int_ty, with_f);
        d.pi_fv(pred_fv, pred_ty, with_a)
    };

    // `sel2 := fun i => mul (sel_a i) (sel_f i)` -- `Int.prodRange_mul`'s
    // own shape (`fun k => mul (f k) (g k)`) at `f := sel_a`, `g := sel_f`.
    let sel2 = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let sa_i = d.apply(sel_a, &[i]);
        let sf_i = d.apply(sel_f, &[i]);
        let body = d.imul(sa_i, sf_i);
        d.lam_fv(i_fv, nat, body)
    };

    // Pointwise: `forall i, Eq Int (sel1 i) (sel2 i)`.
    let pointwise_pf = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let pi = d.apply(pred, &[i]);
        let fi = d.apply(f, &[i]);
        let one_i = d.ione();
        let afi = d.imul(a, fi);

        let motive_lam = {
            let x_fv = d.fresh_fvar();
            let x = d.kernel().fvar(x_fv);
            let lhs_x = bool_select_int(d, x, afi, one_i);
            let sela_x = bool_select_int(d, x, a, one_i);
            let self_x = bool_select_int(d, x, fi, one_i);
            let rhs_x = d.imul(sela_x, self_x);
            let body = d.ieq(lhs_x, rhs_x);
            d.lam_fv(x_fv, bool_ty, body)
        };
        let case_true = d.irefl(afi);
        let case_false = {
            let mul_one_pf = d.const_app(p.mul_one, &[one_i]);
            let oo = d.imul(one_i, one_i);
            d.isymm(oo, one_i, mul_one_pf)
        };
        let level_zero = d.kernel().level_zero();
        let bool_rec = d.int().logic.bool_rec;
        let rec = d.kernel().const_(bool_rec, vec![level_zero]);
        let body = d.apply(rec, &[motive_lam, case_false, case_true, pi]);
        d.lam_fv(i_fv, nat, body)
    };

    let congr_step = d.lemma(p.prod_range_congr, &[sel1, sel2, n, pointwise_pf]);
    // congr_step : Eq Int (prodRange sel1 n) (prodRange sel2 n)

    let mul_step = d.lemma(p.prod_range_mul, &[sel_a, sel_f, n]);
    // mul_step : Eq Int (prodRange sel2 n) (mul (prodRange sel_a n) (prodRange sel_f n))

    let prod_sel1_n = d.const_app(p.prod_range, &[sel1, n]);
    let prod_sel2_n = d.const_app(p.prod_range, &[sel2, n]);
    let (_e, proof) = d.ichain(prod_sel1_n, &[(prod_sel2_n, congr_step), (rhs, mul_step)]);

    let value = {
        let with_n = d.lam_fv(n_fv, nat, proof);
        let with_f = d.lam_fv(f_fv, fn_ty, with_n);
        let with_a = d.lam_fv(a_fv, int_ty, with_f);
        d.lam_fv(pred_fv, pred_ty, with_a)
    };

    d.declare_theorem(p.prod_range_if_factor_const_left, ty, value)
}
