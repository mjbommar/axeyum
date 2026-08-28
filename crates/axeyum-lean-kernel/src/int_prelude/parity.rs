//! `Int.Even`/`Int.Odd`: parity over `ℤ`, defined directly through the
//! already-proved `ℕ` predicates rather than through a fresh `ℤ`-level
//! existential.
//!
//! ## Why `Nat.Even (natAbs n)` / `Nat.Odd (natAbs n)`, not `∃ k : Int, …`
//!
//! Mathlib's `Int.Even`/`Int.Odd` are instances of the generic algebraic
//! definitions (`Even n := ∃ r, n = r + r`, `Odd n := ∃ k, n = 2*k + 1`) at
//! the `Int` type. That form is faithful but does not compose with this
//! kernel's actual entry point into an `Int` proof: every case-split here
//! goes through `Int.rec`'s `ofNat`/`negSucc` constructors (`ops.rs`'s
//! `case_split`), and relating an `Int`-witnessed existential to the
//! already-built `Nat.Even`/`Nat.Odd` (`nat_prelude/parity.rs`) needs a
//! sign argument at every use — exactly the "check what composes" warning
//! the brief for this file carries.
//!
//! Negation does not change parity, so magnitude alone decides it:
//! `Int.Odd n := Nat.Odd (natAbs n)`, `Int.Even n := Nat.Even (natAbs n)`.
//! This is not merely convenient, it is *free* at both constructors, because
//! `natAbs` itself reduces purely on each (`nat_abs.rs`'s module doc):
//!
//! ```text
//! Odd (ofNat a)   ≡ Nat.Odd a          -- natAbs (ofNat a)   ≡ a
//! Odd (negSucc m) ≡ Nat.Odd (succ m)   -- natAbs (negSucc m) ≡ succ m
//! ```
//!
//! and `Nat.Odd (succ m)` is exactly the right-hand side of
//! [`NatPrelude::even_iff_odd_succ`](crate::nat_prelude::NatPrelude::even_iff_odd_succ),
//! so the `negSucc` branch of any `Int.Odd`-hypothesis proof (e.g.
//! `Int.fib_of_odd`, `fibonacci.rs`) reaches `Nat.Even m` through that
//! existing bridge with **no** new `Int`-level parity lemma at all — matching
//! the earlier lane's prediction exactly, and confirming it: no `Int`-level
//! parity reasoning is needed to use the predicate once it is stated this
//! way.
//!
//! [`declare_odd_iff_nat_abs_odd`]/[`declare_even_iff_nat_abs_even`] are the
//! two bridge lemmas the brief asks for. Both are near-tautological (`fun h
//! => h` in each direction) precisely *because* the definition above already
//! **is** the bridge; they exist as named, discoverable API surface rather
//! than to do any work a caller could not get by unfolding the definition
//! directly.

use crate::KernelError;
use crate::env::{Declaration, ReducibilityHint};
use crate::expr::ExprId;
use crate::nat_prelude::NatOps;

use super::ops::IntDev;

/// `Int.natAbs a`. Module-private mirror of `gcd.rs`'s/`bezout_witnesses.rs`'s
/// own copies (`nat_abs.rs`'s `NatAbsOps` trait is private to that module).
fn nat_abs(d: &mut IntDev<'_>, a: ExprId) -> ExprId {
    let f = d.int().nat_abs;
    d.const_app(f, &[a])
}

/// Height for `Int.Even`/`Int.Odd`: each unfolds through exactly one
/// `Int.natAbs` application (local height 4 within `nat_abs.rs`) to a
/// `Nat.Even`/`Nat.Odd` application (height 4 within `nat_prelude/parity.rs`),
/// so 5 strictly dominates both direct callees.
const EVEN_ODD_HEIGHT: u16 = 5;

/// `Int.Even`, `Int.Odd` — see the module doc for why magnitude alone
/// decides parity.
fn declare_even_odd_defs(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    let int_ty = d.int_ty();
    let prop = d.kernel().sort_zero();

    // Even n := Nat.Even (natAbs n)
    {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let mag = nat_abs(d, n);
        let body = d.const_app(p.nat.even, &[mag]);
        let value = d.lam_fv(n_fv, int_ty, body);
        let ty = d.arrow(int_ty, prop);
        d.kernel().add_declaration(Declaration::Definition {
            name: p.even,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(EVEN_ODD_HEIGHT),
        })?;
    }

    // Odd n := Nat.Odd (natAbs n)
    {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let mag = nat_abs(d, n);
        let body = d.const_app(p.nat.odd, &[mag]);
        let value = d.lam_fv(n_fv, int_ty, body);
        let ty = d.arrow(int_ty, prop);
        d.kernel().add_declaration(Declaration::Definition {
            name: p.odd,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(EVEN_ODD_HEIGHT),
        })?;
    }
    Ok(())
}

/// `Int.odd_iff_nat_abs_odd : ∀ n, Iff (Odd n) (Nat.Odd (natAbs n))`. Both
/// directions are the identity function, since the two sides are the SAME
/// term up to one delta unfold of `Int.Odd` — see the module doc.
fn declare_odd_iff_nat_abs_odd(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();

    d.int_theorem(p.odd_iff_nat_abs_odd, 1, &|d, v| {
        let n = v[0];
        let odd_n_ty = d.const_app(p.odd, &[n]);
        let mag = nat_abs(d, n);
        let nat_odd_mag_ty = d.const_app(p.nat.odd, &[mag]);
        let stmt = d.const_app(p.logic.iff, &[odd_n_ty, nat_odd_mag_ty]);

        let mp = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            d.lam_fv(h_fv, odd_n_ty, h)
        };
        let mpr = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            d.lam_fv(h_fv, nat_odd_mag_ty, h)
        };
        let proof = d.const_app(p.logic.iff_intro, &[odd_n_ty, nat_odd_mag_ty, mp, mpr]);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Int.even_iff_nat_abs_even : ∀ n, Iff (Even n) (Nat.Even (natAbs n))` —
/// [`declare_odd_iff_nat_abs_odd`] with `Even`/`Odd` swapped; no new
/// construction.
fn declare_even_iff_nat_abs_even(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();

    d.int_theorem(p.even_iff_nat_abs_even, 1, &|d, v| {
        let n = v[0];
        let even_n_ty = d.const_app(p.even, &[n]);
        let mag = nat_abs(d, n);
        let nat_even_mag_ty = d.const_app(p.nat.even, &[mag]);
        let stmt = d.const_app(p.logic.iff, &[even_n_ty, nat_even_mag_ty]);

        let mp = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            d.lam_fv(h_fv, even_n_ty, h)
        };
        let mpr = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            d.lam_fv(h_fv, nat_even_mag_ty, h)
        };
        let proof = d.const_app(p.logic.iff_intro, &[even_n_ty, nat_even_mag_ty, mp, mpr]);
        (stmt, proof)
    })?;
    Ok(())
}

/// Declare every theorem in this module.
pub(super) fn declare_parity_all(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    declare_even_odd_defs(d)?;
    declare_odd_iff_nat_abs_odd(d)?;
    declare_even_iff_nat_abs_even(d)?;
    Ok(())
}
