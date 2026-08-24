//! `Rat.decidable_le : ∀ a b, Decidable (Rat.le a b)` — the `logic` prelude's
//! `Decidable.ofBool` bridge (`crates/axeyum-lean-kernel/src/prelude.rs`)
//! applied to `Rat.ble` (`super::decide`) and its already-proved spec
//! directions, the same pattern `string_prelude/decidable.rs` uses for
//! `Char.decidable_eq` / `Str.decidable_eq` / `Str.decidable_isPrefix`: a
//! `Bool`-valued decision plus its positive (`ble = true → le`) and
//! completeness (`le → ble = true`) directions is exactly what
//! `Decidable.ofBool` needs.
//!
//! # The negative direction, again
//!
//! `Decidable.ofBool` needs BOTH `(b = true → p)` and `(b = false → ¬p)`;
//! `super::decide` only proves the converse pair
//! ([`RatPrelude::le_of_ble_eq_true`](super::RatPrelude::le_of_ble_eq_true),
//! [`RatPrelude::ble_eq_true_of_le`](super::RatPrelude::ble_eq_true_of_le)),
//! so — exactly as `string_prelude/decidable.rs`'s module doc explains for its
//! own three instances — the negative direction is derived by contraposition
//! rather than proved directly: given `hf : Rat.ble a b = false` and
//! `hp : Rat.le a b`, [`RatPrelude::ble_eq_true_of_le`] turns `hp` into
//! `hc : Rat.ble a b = true`; `hf` and `hc` share the left-hand side
//! `Rat.ble a b`, so [`crate::nat_prelude::NatOps::bool_symm`] and
//! [`crate::nat_prelude::NatOps::bool_trans`] compose them (one hop each) into
//! `Eq Bool Bool.false Bool.true`, closed by
//! [`crate::nat_prelude::NatOps::false_true_elim`]. This kernel has no
//! `Eq.trans` anywhere (`string_prelude/decidable.rs`'s own module doc), but
//! `bool_symm`/`bool_trans` are themselves built from a single `Eq.rec`
//! application each (`nat_prelude/ops.rs`), so no representation-level case
//! split is needed here — everything is applying already-proved lemmas and
//! generic `Bool`-equality combinators.
//!
//! No new case split on `Rat`'s representation is needed: unlike
//! [`super::decide`]'s own `Rat.ble` (which case-splits `Int.rec` on the
//! cross-multiplication gap) or the constructive trichotomy
//! ([`RatPrelude::le_or_lt`](super::RatPrelude::le_or_lt)), this file adds no
//! new decision procedure — it only repackages the one `super::decide`
//! already built as a `Decidable` instance.

use super::RatPrelude;
use super::ops::{rat_ty, rle};
use crate::KernelError;
use crate::env::{Declaration, ReducibilityHint};
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::NatOps;

/// Delta height for `Rat.decidable_le`: above `Rat.ble`
/// (`decide.rs`'s `BLE_HEIGHT`, 33) and its spec
/// (`Rat.ble_eq_true_of_le`/`Rat.le_of_ble_eq_true`, declared alongside it).
const DECIDABLE_LE_HEIGHT: u16 = 34;

/// `Eq Bool (Rat.ble a b) Bool.false → Rat.le a b → False` — the negative
/// direction [`declare_decidable_le`] needs, by contraposition against
/// [`RatPrelude::ble_eq_true_of_le`]. See this module's doc for the
/// `bool_symm`/`bool_trans`/`false_true_elim` derivation.
fn decidable_le_neg(d: &mut IntDev<'_>, p: RatPrelude, a: ExprId, b: ExprId) -> ExprId {
    let ble_ab = d.const_app(p.ble, &[a, b]);
    let false_ = d.bool_false();
    let true_ = d.bool_true();

    let hf_fv = d.fresh_fvar();
    let hf = d.kernel().fvar(hf_fv);
    let hp_fv = d.fresh_fvar();
    let hp = d.kernel().fvar(hp_fv);

    // hc : Eq Bool (ble a b) true, from hp via completeness.
    let hc = d.lemma(p.ble_eq_true_of_le, &[a, b, hp]);
    // symm_hf : Eq Bool false (ble a b), from hf.
    let symm_hf = d.bool_symm(ble_ab, false_, hf);
    // combined : Eq Bool false true.
    let combined = d.bool_trans(false_, ble_ab, true_, symm_hf, hc);
    let false_ty = d.false_ty();
    let contradiction = d.false_true_elim(false_ty, combined);

    let hp_ty = rle(d, p, a, b);
    let with_hp = d.lam_fv(hp_fv, hp_ty, contradiction);
    let hf_ty = d.bool_eq(ble_ab, false_);
    d.lam_fv(hf_fv, hf_ty, with_hp)
}

/// Admit `Rat.decidable_le : ∀ a b, Decidable (Rat.le a b) := fun a b =>
/// Decidable.ofBool (Rat.le a b) (Rat.ble a b)
///   (fun h => Rat.le_of_ble_eq_true a b h)
///   (decidable_le_neg a b)`.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
fn declare_decidable_le(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let carrier = rat_ty(d);

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);

    let le_ab = rle(d, p, a, b);
    let decidable_name = d.prelude().logic.decidable;
    let decidable_const = d.kernel().const_(decidable_name, vec![]);
    let dec_le_ab = d.kernel().app(decidable_const, le_ab);

    // type: Π (a b : Rat), Decidable (Rat.le a b).
    let with_b = d.pi_fv(b_fv, carrier, dec_le_ab);
    let ty = d.pi_fv(a_fv, carrier, with_b);

    let ble_ab = d.const_app(p.ble, &[a, b]);
    let true_ = d.bool_true();

    let pos_fn = {
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let h_ty = d.bool_eq(ble_ab, true_);
        let body = d.lemma(p.le_of_ble_eq_true, &[a, b, h]);
        d.lam_fv(h_fv, h_ty, body)
    };
    let neg_fn = decidable_le_neg(d, p, a, b);

    let of_bool_name = d.prelude().logic.decidable_of_bool;
    let of_bool = d.kernel().const_(of_bool_name, vec![]);
    let body = d.apply(of_bool, &[le_ab, ble_ab, pos_fn, neg_fn]);

    let value_with_b = d.lam_fv(b_fv, carrier, body);
    let value = d.lam_fv(a_fv, carrier, value_with_b);

    d.kernel().add_declaration(Declaration::Definition {
        name: p.decidable_le,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(DECIDABLE_LE_HEIGHT),
    })
}

/// Admit `Rat.decidable_le`.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
pub(super) fn declare_decidable(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    declare_decidable_le(d, p)
}
