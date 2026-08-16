//! `Rat` — the rational numbers, as a **normalised structure** over the proved
//! `ℤ` and `ℕ` developments.
//!
//! ## Why a structure and not a quotient
//!
//! The textbook construction is a setoid quotient of `ℤ × ℤ≠0` by
//! cross-multiplication. In *this* kernel that is not merely expensive, it is
//! **inexpressible**: the quotient package is four declarations — `Quot`,
//! `Quot.mk`, `Quot.lift`, `Quot.ind` — with **no `Quot.sound`**, so nothing can
//! prove two `Quot.mk`s equal (ADR-0456).
//!
//! Lean 4.30.0's own source, read rather than guessed, does not use a quotient
//! either (`Init/Data/Rat/Basic.lean`):
//!
//! ```text
//! structure Rat where
//!   num : Int
//!   den : Nat := 1
//!   den_nz : den ≠ 0
//!   reduced : num.natAbs.Coprime den
//! ```
//!
//! A normalised representative plus two proof fields. That is the same move
//! `Int` already makes here — `ofNat`/`negSucc` give every integer exactly one
//! representative — so `Eq Rat` is ordinary propositional equality and a derived
//! law's axiom footprint stays genuinely empty.
//!
//! ## The two proof fields
//!
//! - **Positivity** is stated as `1 ≤ den` rather than Lean's `den ≠ 0`. Our
//!   order development produces and consumes `Nat.le (succ zero) d` directly —
//!   it is the shape `div_mod_exists`, `mul_left_cancel_of_pos` and
//!   `dvd_add_right_cancel_of_pos` all take — whereas `≠ 0` would have to be
//!   converted at every use. The two are equivalent over `ℕ`; this one is free.
//! - **Reducedness** is `gcd (natAbs num) den = 1`, discharged for a concrete
//!   rational by `rfl`, because `Nat.gcd` is executable.
//!
//! ## Where this lives
//!
//! Inside the integer prelude, for now. ADR-0001's rule is that a boundary is
//! added once it is *proven by use*, and that applies to a new prelude as much
//! as to a new crate: `IntDev` already carries both the `Int` and `Nat` names
//! this needs, and nothing yet consumes `Rat` from outside.

use crate::KernelError;
use crate::expr::BinderInfo;
use crate::nat_prelude::NatOps;

use super::ops::IntDev;

/// Admit `Rat : Type` with its single normalising constructor.
///
/// ```text
/// Rat.mk : (num : Int) → (den : Nat) → 1 ≤ den →
///          gcd (natAbs num) den = 1 → Rat
/// ```
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructor's telescope does not
/// check — in particular if a proof field's type mentions a later field.
pub(super) fn declare_rat(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    let nat = d.nat_ty();
    let int_ty = d.int_ty();
    let one = d.level_one();
    let type1 = d.kernel().sort(one);
    let rat_ty = d.kernel().const_(p.rat, vec![]);

    let num_fv = d.fresh_fvar();
    let num = d.kernel().fvar(num_fv);
    let den_fv = d.fresh_fvar();
    let den = d.kernel().fvar(den_fv);

    // `1 ≤ den`, the positivity the ℕ division and cancellation lemmas take.
    let positive = {
        let zero = d.zero();
        let unit = d.succ(zero);
        NatOps::le(d, unit, den)
    };
    // `gcd (natAbs num) den = 1`, reducible to `rfl` at a concrete rational.
    let reduced = {
        let magnitude = d.const_app(p.nat_abs, &[num]);
        let common = NatOps::gcd(d, magnitude, den);
        let zero = d.zero();
        let unit = d.succ(zero);
        d.eq(common, unit)
    };

    let anon = d.anon_name();
    let ctor_ty = {
        let after_reduced = d.kernel().pi(anon, reduced, rat_ty, BinderInfo::Default);
        let after_positive = d
            .kernel()
            .pi(anon, positive, after_reduced, BinderInfo::Default);
        let after_den = d.pi_fv(den_fv, nat, after_positive);
        d.pi_fv(num_fv, int_ty, after_den)
    };

    d.kernel()
        .add_inductive(p.rat, &[], 0, type1, &[(p.rat_mk, ctor_ty)])
}
