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

use crate::NatOps;
use crate::int_prelude::ops::IntDev;

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
