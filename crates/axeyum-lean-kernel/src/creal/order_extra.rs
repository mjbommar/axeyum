//! `CReal.eq_zero_of_add_eq_zero_of_nonneg` — nonnegative summands of a zero
//! sum are each zero, over the constructed reals.
//!
//! This is an ordinary ordered-field fact (`0 ≤ a → 0 ≤ b → a + b ~ 0 → a ~
//! 0`) that `creal.rs`'s order block (`declare_order`/`declare_strict_order`)
//! did not need for itself but that downstream developments — starting with
//! `CPoint.dot_self_zero_iff`, positive-definiteness of the dot product over
//! the constructed plane — do. It belongs here rather than in
//! `creal_point.rs` because nothing about it mentions `CPoint`; it is a fact
//! about the field.
//!
//! ## The route
//!
//! `CReal.le` is Bishop's order and `CReal.equiv_of_le_le` is antisymmetry up
//! to `Equiv` (`le x y → le y x → Equiv x y`) — exactly the closing step. The
//! rest is order algebra with no analytic content, so no index/regularity
//! reasoning is needed here at all:
//!
//! 1. `add_le_add (le_refl a) (h_b : le zero b)` gives
//!    `le (add a zero) (add a b)`.
//! 2. `le_congr` transports that across `add_zero : Equiv (add a zero) a` (on
//!    the left) and `equiv_refl (add a b)` (on the right, unchanged) to get
//!    `le a (add a b)`.
//! 3. `le_of_equiv` reads the hypothesis `Equiv (add a b) zero` as
//!    `le (add a b) zero`.
//! 4. `le_trans` chains 2 and 3: `le a zero`.
//! 5. `equiv_of_le_le a zero` applied to 4 and `h_a : le zero a` closes
//!    `Equiv a zero`.

use crate::KernelError;
use crate::env::Declaration;
use crate::expr::ExprId;

use crate::NatOps;
use crate::int_prelude::ops::IntDev;
use crate::rat_prelude::ops::rat_ty;

use super::{CRealPrelude, creal_ty, equiv};

pub(super) fn declare_order_extra(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);

    let zero_real = d.kernel().const_(p.zero, vec![]);
    let sum = d.const_app(p.add, &[a, b]);

    let ha_ty = d.const_app(p.le, &[zero_real, a]);
    let ha_fv = d.fresh_fvar();
    let ha = d.kernel().fvar(ha_fv);

    let hb_ty = d.const_app(p.le, &[zero_real, b]);
    let hb_fv = d.fresh_fvar();
    let hb = d.kernel().fvar(hb_fv);

    let hab_ty = equiv(d, p, sum, zero_real);
    let hab_fv = d.fresh_fvar();
    let hab = d.kernel().fvar(hab_fv);

    // Step 1: le (add a zero) (add a b), from le_refl a and hb.
    let a_plus_zero = d.const_app(p.add, &[a, zero_real]);
    let refl_a = d.lemma(p.le_refl, &[a]);
    let shifted = d.lemma(p.add_le_add, &[a, a, zero_real, b, refl_a, hb]);
    // shifted : le (add a zero) (add a b)

    // Step 2: le a (add a b), transporting `shifted` across `add_zero` on the
    // left and reflexivity on the right.
    let restore = d.lemma(p.add_zero, &[a]);
    // restore : Equiv (add a zero) a
    let sum_refl = d.lemma(p.equiv_refl, &[sum]);
    // sum_refl : Equiv (add a b) (add a b)
    let a_le_sum = d.lemma(
        p.le_congr,
        &[a_plus_zero, a, sum, sum, restore, sum_refl, shifted],
    );
    // a_le_sum : le a (add a b)

    // Step 3: le (add a b) zero, from the hypothesis a + b ~ 0.
    let sum_le_zero = d.lemma(p.le_of_equiv, &[sum, zero_real, hab]);

    // Step 4: le a zero.
    let a_le_zero = d.lemma(p.le_trans, &[a, sum, zero_real, a_le_sum, sum_le_zero]);

    // Step 5: Equiv a zero, by antisymmetry.
    let body = d.lemma(p.equiv_of_le_le, &[a, zero_real, a_le_zero, ha]);

    let value = {
        let with_hab = d.lam_fv(hab_fv, hab_ty, body);
        let with_hb = d.lam_fv(hb_fv, hb_ty, with_hab);
        let with_ha = d.lam_fv(ha_fv, ha_ty, with_hb);
        let with_b = d.lam_fv(b_fv, carrier, with_ha);
        d.lam_fv(a_fv, carrier, with_b)
    };
    let ty = {
        let conclusion = equiv(d, p, a, zero_real);
        let after_hab = d.arrow(hab_ty, conclusion);
        let after_hb = d.arrow(hb_ty, after_hab);
        let after_ha = d.arrow(ha_ty, after_hb);
        let with_b = d.pi_fv(b_fv, carrier, after_ha);
        d.pi_fv(a_fv, carrier, with_b)
    };

    d.kernel().add_declaration(Declaration::Theorem {
        name: p.eq_zero_of_add_eq_zero_of_nonneg,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.neg_sub_swap` and `CReal.abs_le_of_two_sided` — a SECOND entry
/// point, dispatched after `lattice::declare_lattice` in `creal.rs`'s build
/// order (`declare_order_extra` above runs before `lattice`, and both new
/// declarations need `CReal.abs`/`CReal.abs_le`; `neg_sub_swap` itself does
/// not, but is dispatched alongside its only consumer rather than splitting
/// the pair across two additional entry points).
pub(super) fn declare_order_extra_abs(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    declare_neg_sub_swap(d, p)?;
    declare_abs_le_of_two_sided(d, p)
}

// --- `CReal.neg_sub_swap` / `CReal.abs_le_of_two_sided` ----------------------
//
// Added for `creal/uniform_convergence.rs` (Spivak Ch24): reconstructing a
// `close_within (G x) (G y) q`-shaped conclusion (the shape
// `UniformlyContinuousOn.spec` both consumes and produces) from a triangle of
// intermediate `close_within` facts needs relating `neg (add a (neg b))` to
// `add b (neg a)` -- negating a difference reverses it -- and this development
// had no public `neg_add`/`neg_neg` pair to build that from (each of
// `series.rs`/`derivative.rs`/`uniform_continuity.rs`/`deriv_unique.rs` keeps
// only a PRIVATE `neg_add` copy, per `ring_helpers.rs`'s documented policy of
// not sharing that one further). Rather than adding a fifth private copy (or
// widening one, which is not this session's file to touch), [`neg_sub_swap`]
// proves the SPECIFIC compound fact needed directly, via uniqueness of the
// additive inverse (both `add a (neg b)` and its own `neg` are, trivially,
// each other's inverse under `add`, and `add b (neg a)` is ALSO an inverse of
// `add a (neg b)` by a pure `add_comm`/`add_assoc` rearrangement -- two
// inverses of the same element are `Equiv`) -- no `neg_add`/`neg_neg` pair is
// derived as a separate fact, only the one compound identity this file's own
// consumer needs. [`declare_abs_le_of_two_sided`] is the genuine converse of
// `creal/integral.rs`'s own `CReal.two_sided_of_abs_sub_le` (that direction
// splits a `close_within` into two one-sided `le`s; this direction rebuilds a
// `close_within` from two one-sided `le`s in the "shifted" `x <= y + q` form),
// and belongs here rather than in `integral.rs` for the same reason
// `eq_zero_of_add_eq_zero_of_nonneg` does: ordinary order algebra, no
// analytic content, `integral.rs` is not this session's file.

/// `Equiv (add zero x) x` — commute into `add_zero`'s own shape.
fn zero_add_equiv(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId) -> ExprId {
    let zero = d.kernel().const_(p.zero, vec![]);
    let zx = d.const_app(p.add, &[zero, x]);
    let xz = d.const_app(p.add, &[x, zero]);
    let comm = d.lemma(p.add_comm, &[zero, x]); // Equiv zx xz
    let az = d.lemma(p.add_zero, &[x]); // Equiv xz x
    d.lemma(p.equiv_trans, &[zx, xz, x, comm, az])
}

/// From `f1 : Equiv (add w b) zero` and `f2 : Equiv (add w c) zero`, derive
/// `Equiv b c` — uniqueness of `w`'s additive inverse.
fn additive_cancel(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    w: ExprId,
    b: ExprId,
    c: ExprId,
    f1: ExprId,
    f2: ExprId,
) -> ExprId {
    let zero = d.kernel().const_(p.zero, vec![]);
    let wc = d.const_app(p.add, &[w, c]);

    // step1 : Equiv b (add b zero)
    let b_zero = d.const_app(p.add, &[b, zero]);
    let step1 = {
        let h = d.lemma(p.add_zero, &[b]); // Equiv b_zero b
        d.lemma(p.equiv_symm, &[b_zero, b, h])
    };
    // step2 : Equiv (add b zero) (add b (add w c)) via f2 symm.
    let b_wc = d.const_app(p.add, &[b, wc]);
    let step2 = {
        let f2s = d.lemma(p.equiv_symm, &[wc, zero, f2]); // Equiv zero wc
        let refl_b = d.lemma(p.equiv_refl, &[b]);
        d.lemma(p.add_congr, &[b, b, zero, wc, refl_b, f2s])
    };
    // step3 : Equiv (add b (add w c)) (add (add b w) c) — assoc, reversed.
    let bw = d.const_app(p.add, &[b, w]);
    let bw_c = d.const_app(p.add, &[bw, c]);
    let step3 = {
        let assoc = d.lemma(p.add_assoc, &[b, w, c]); // Equiv bw_c b_wc
        d.lemma(p.equiv_symm, &[bw_c, b_wc, assoc])
    };
    // step4 : Equiv (add (add b w) c) (add (add w b) c) — commute inside.
    let wb = d.const_app(p.add, &[w, b]);
    let wb_c = d.const_app(p.add, &[wb, c]);
    let step4 = {
        let comm = d.lemma(p.add_comm, &[b, w]); // Equiv bw wb
        let refl_c = d.lemma(p.equiv_refl, &[c]);
        d.lemma(p.add_congr, &[bw, wb, c, c, comm, refl_c])
    };
    // step5 : Equiv (add (add w b) c) (add zero c) via f1.
    let zero_c = d.const_app(p.add, &[zero, c]);
    let step5 = {
        let refl_c = d.lemma(p.equiv_refl, &[c]);
        d.lemma(p.add_congr, &[wb, zero, c, c, f1, refl_c])
    };
    let step6 = zero_add_equiv(d, p, c);

    let s12 = d.lemma(p.equiv_trans, &[b, b_zero, b_wc, step1, step2]);
    let s123 = d.lemma(p.equiv_trans, &[b, b_wc, bw_c, s12, step3]);
    let s1234 = d.lemma(p.equiv_trans, &[b, bw_c, wb_c, s123, step4]);
    let s12345 = d.lemma(p.equiv_trans, &[b, wb_c, zero_c, s1234, step5]);
    d.lemma(p.equiv_trans, &[b, zero_c, c, s12345, step6])
}

/// `Equiv (neg (add a (neg b))) (add b (neg a))` — negating a difference
/// reverses it. See the section documentation above.
fn neg_sub_swap_proof(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId, b: ExprId) -> ExprId {
    let zero = d.kernel().const_(p.zero, vec![]);
    let na = d.const_app(p.neg, &[a]);
    let nb = d.const_app(p.neg, &[b]);
    let w = d.const_app(p.add, &[a, nb]); // a + (-b)
    let nw = d.const_app(p.neg, &[w]);
    let c = d.const_app(p.add, &[b, na]); // b + (-a)

    let f1 = d.lemma(p.add_neg, &[w]); // Equiv (add w nw) zero

    // f2 : Equiv (add w c) zero.
    let f2 = {
        let wc = d.const_app(p.add, &[w, c]);
        let nb_c = d.const_app(p.add, &[nb, c]);
        let a_nbc = d.const_app(p.add, &[a, nb_c]);
        let step_assoc = d.lemma(p.add_assoc, &[a, nb, c]); // Equiv wc a_nbc

        let nb_b = d.const_app(p.add, &[nb, b]);
        let na_arg = na;
        let nbb_na = d.const_app(p.add, &[nb_b, na_arg]);
        let inner_assoc = d.lemma(p.add_assoc, &[nb, b, na_arg]); // Equiv nbb_na nb_c
        let step_inner1 = d.lemma(p.equiv_symm, &[nbb_na, nb_c, inner_assoc]); // Equiv nb_c nbb_na

        let nbb_zero = {
            let b_nb = d.const_app(p.add, &[b, nb]);
            let comm = d.lemma(p.add_comm, &[nb, b]); // Equiv nb_b b_nb
            let negeq = d.lemma(p.add_neg, &[b]); // Equiv b_nb zero
            d.lemma(p.equiv_trans, &[nb_b, b_nb, zero, comm, negeq])
        };
        let zero_na = d.const_app(p.add, &[zero, na_arg]);
        let step_inner3 = {
            let refl_na = d.lemma(p.equiv_refl, &[na_arg]);
            d.lemma(
                p.add_congr,
                &[nb_b, zero, na_arg, na_arg, nbb_zero, refl_na],
            )
        };
        let step_inner4 = zero_add_equiv(d, p, na_arg); // Equiv zero_na na_arg

        let i12 = d.lemma(
            p.equiv_trans,
            &[nb_c, nbb_na, zero_na, step_inner1, step_inner3],
        );
        let i123 = d.lemma(p.equiv_trans, &[nb_c, zero_na, na_arg, i12, step_inner4]);
        // i123 : Equiv nb_c na_arg

        let a_na = d.const_app(p.add, &[a, na_arg]);
        let step_outer = {
            let refl_a = d.lemma(p.equiv_refl, &[a]);
            d.lemma(p.add_congr, &[a, a, nb_c, na_arg, refl_a, i123])
        };
        let final_eq = d.lemma(p.add_neg, &[a]); // Equiv a_na zero

        let o1 = d.lemma(p.equiv_trans, &[wc, a_nbc, a_na, step_assoc, step_outer]);
        d.lemma(p.equiv_trans, &[wc, a_na, zero, o1, final_eq])
    };

    additive_cancel(d, p, w, nw, c, f1, f2)
}

/// `CReal.neg_sub_swap : ∀ a b, Equiv (neg (add a (neg b))) (add b (neg a))`.
fn declare_neg_sub_swap(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);

    let body = neg_sub_swap_proof(d, p, a, b);
    let value = {
        let with_b = d.lam_fv(b_fv, carrier, body);
        d.lam_fv(a_fv, carrier, with_b)
    };
    let ty = {
        let na = d.const_app(p.neg, &[a]);
        let nb = d.const_app(p.neg, &[b]);
        let w = d.const_app(p.add, &[a, nb]);
        let nw = d.const_app(p.neg, &[w]);
        let c = d.const_app(p.add, &[b, na]);
        let conclusion = equiv(d, p, nw, c);
        let with_b = d.pi_fv(b_fv, carrier, conclusion);
        d.pi_fv(a_fv, carrier, with_b)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.neg_sub_swap,
        uparams: vec![],
        ty,
        value,
    })
}

/// `Equiv (add (add y q) (neg y)) q` — adding then subtracting the same term
/// cancels, leaving the other summand `q` in place.
fn add_sub_self_cancel(d: &mut IntDev<'_>, p: CRealPrelude, y: ExprId, q: ExprId) -> ExprId {
    let zero = d.kernel().const_(p.zero, vec![]);
    let ny = d.const_app(p.neg, &[y]);
    let yq = d.const_app(p.add, &[y, q]);
    let yq_ny = d.const_app(p.add, &[yq, ny]);

    let qy = d.const_app(p.add, &[q, y]);
    let qy_ny = d.const_app(p.add, &[qy, ny]);
    let comm1 = d.lemma(p.add_comm, &[y, q]); // Equiv yq qy
    let refl_ny = d.lemma(p.equiv_refl, &[ny]);
    let step1 = d.lemma(p.add_congr, &[yq, qy, ny, ny, comm1, refl_ny]); // Equiv yq_ny qy_ny

    let y_ny = d.const_app(p.add, &[y, ny]);
    let q_yny = d.const_app(p.add, &[q, y_ny]);
    let assoc = d.lemma(p.add_assoc, &[q, y, ny]); // Equiv qy_ny q_yny

    let y_neg = d.lemma(p.add_neg, &[y]); // Equiv y_ny zero
    let refl_q = d.lemma(p.equiv_refl, &[q]);
    let step3 = d.lemma(p.add_congr, &[q, q, y_ny, zero, refl_q, y_neg]); // Equiv q_yny (add q zero)
    let q_zero = d.const_app(p.add, &[q, zero]);
    let step4 = d.lemma(p.add_zero, &[q]); // Equiv q_zero q

    let s12 = d.lemma(p.equiv_trans, &[yq_ny, qy_ny, q_yny, step1, assoc]);
    let s123 = d.lemma(p.equiv_trans, &[yq_ny, q_yny, q_zero, s12, step3]);
    d.lemma(p.equiv_trans, &[yq_ny, q_zero, q, s123, step4])
}

/// `CReal.abs_le_of_two_sided : ∀ x y q : Rat, le x (add y (ofRat q)) →
/// le y (add x (ofRat q)) → le (abs (add x (neg y))) (ofRat q)` — the
/// converse of `creal/integral.rs`'s `CReal.two_sided_of_abs_sub_le`.
fn declare_abs_le_of_two_sided(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let rat_carrier = rat_ty(d);

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);
    let q_fv = d.fresh_fvar();
    let q = d.kernel().fvar(q_fv);
    let q_real = d.const_app(p.of_rat, &[q]);

    let y_plus_q = d.const_app(p.add, &[y, q_real]);
    let hxy_ty = d.const_app(p.le, &[x, y_plus_q]);
    let hxy_fv = d.fresh_fvar();
    let hxy = d.kernel().fvar(hxy_fv);

    let x_plus_q = d.const_app(p.add, &[x, q_real]);
    let hyx_ty = d.const_app(p.le, &[y, x_plus_q]);
    let hyx_fv = d.fresh_fvar();
    let hyx = d.kernel().fvar(hyx_fv);

    let ny = d.const_app(p.neg, &[y]);
    let nx = d.const_app(p.neg, &[x]);
    let w = d.const_app(p.add, &[x, ny]); // x + (-y)

    // leg1 : le w q_real
    let leg1 = {
        let refl_ny = d.lemma(p.le_refl, &[ny]);
        let shifted = d.lemma(p.add_le_add, &[x, y_plus_q, ny, ny, hxy, refl_ny]);
        // shifted : le w (add y_plus_q ny)
        let rearr = add_sub_self_cancel(d, p, y, q_real); // Equiv (add y_plus_q ny) q_real
        let shifted_rhs = d.const_app(p.add, &[y_plus_q, ny]);
        let refl_w = d.lemma(p.equiv_refl, &[w]);
        d.lemma(
            p.le_congr,
            &[w, w, shifted_rhs, q_real, refl_w, rearr, shifted],
        )
    };

    // leg2_pre : le (add y nx) q_real
    let y_nx = d.const_app(p.add, &[y, nx]);
    let leg2_pre = {
        let refl_nx = d.lemma(p.le_refl, &[nx]);
        let shifted = d.lemma(p.add_le_add, &[y, x_plus_q, nx, nx, hyx, refl_nx]);
        // shifted : le y_nx (add x_plus_q nx)
        let rearr = add_sub_self_cancel(d, p, x, q_real); // Equiv (add x_plus_q nx) q_real
        let shifted_rhs = d.const_app(p.add, &[x_plus_q, nx]);
        let refl_ynx = d.lemma(p.equiv_refl, &[y_nx]);
        d.lemma(
            p.le_congr,
            &[y_nx, y_nx, shifted_rhs, q_real, refl_ynx, rearr, shifted],
        )
    };
    // leg2 : le (neg w) q_real, via neg_sub_swap.
    let nw = d.const_app(p.neg, &[w]);
    let leg2 = {
        let swap = d.lemma(p.neg_sub_swap, &[x, y]); // Equiv nw y_nx
        let swap_symm = d.lemma(p.equiv_symm, &[nw, y_nx, swap]); // Equiv y_nx nw
        let refl_q = d.lemma(p.equiv_refl, &[q_real]);
        d.lemma(
            p.le_congr,
            &[y_nx, nw, q_real, q_real, swap_symm, refl_q, leg2_pre],
        )
    };

    let body = d.lemma(p.abs_le, &[w, q_real, leg1, leg2]);

    let value = {
        let with_hyx = d.lam_fv(hyx_fv, hyx_ty, body);
        let with_hxy = d.lam_fv(hxy_fv, hxy_ty, with_hyx);
        let with_q = d.lam_fv(q_fv, rat_carrier, with_hxy);
        let with_y = d.lam_fv(y_fv, carrier, with_q);
        d.lam_fv(x_fv, carrier, with_y)
    };
    let ty = {
        let abs_w = d.const_app(p.abs, &[w]);
        let conclusion = d.const_app(p.le, &[abs_w, q_real]);
        let after_hyx = d.arrow(hyx_ty, conclusion);
        let after_hxy = d.arrow(hxy_ty, after_hyx);
        let with_q = d.pi_fv(q_fv, rat_carrier, after_hxy);
        let with_y = d.pi_fv(y_fv, carrier, with_q);
        d.pi_fv(x_fv, carrier, with_y)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.abs_le_of_two_sided,
        uparams: vec![],
        ty,
        value,
    })
}
