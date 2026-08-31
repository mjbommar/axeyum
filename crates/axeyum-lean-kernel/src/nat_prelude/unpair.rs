//! `Nat.unpairLeft`, `Nat.unpairRight` and `Nat.unpaired` — the inverse of
//! [`Nat.pair`](super::avg_pair), without `Prod`.
//!
//! # Why this exists, and why it is three definitions rather than one
//!
//! [`avg_pair.rs`](super::avg_pair)'s module doc records `Nat.unpair` as
//! **unreachable here**, and that reading is correct as far as it goes:
//! Mathlib's `Nat.unpair : Nat → Nat × Nat` returns a `Prod`, and this
//! kernel has no `Prod` (the complete inductive list is `True`/`False`/
//! `And`/`Or`/`Iff`/`Eq`/`Exists`/`Acc`/`Bool`/`Nat`/`Decidable` + `Nat.le`
//! + `Nat.Fin` + `Char` + `Nat.Pair`). So `Nat.unpair` itself stays out of
//! reach, and every `ml430` mirror stated over it stays `open`.
//!
//! What does NOT follow is that the *unpairing* is out of reach. The
//! standing workaround for a pair in this prelude is to split the
//! projections into separate scalar functions — the same move
//! `Nat.xgcdAux (sel : Bool)`, `Nat.divModState` and `creal/ivt.rs`'s
//! `Bool → CReal` already make — and both projections have type `Nat → Nat`,
//! which mentions no product at all. `Nat.unpaired`, the consumer that
//! actually appears in Mathlib statements, then has Mathlib's own type
//! `(Nat → Nat → Nat) → Nat → Nat` with no `Prod` in it either: only the
//! BODY of Mathlib's version mentions `unpair`, and ours does not have to.
//!
//! ```text
//! Nat.unpairLeft  (n : Nat) : Nat
//!   := let s := sqrt n; let r := n - s * s
//!      in if r < s then r else s
//! Nat.unpairRight (n : Nat) : Nat
//!   := let s := sqrt n; let r := n - s * s
//!      in if r < s then s else r - s
//! Nat.unpaired (f : Nat → Nat → Nat) (n : Nat) : Nat
//!   := f (Nat.unpairLeft n) (Nat.unpairRight n)
//! ```
//!
//! These are Lean 4 core's own `Nat.unpair` branches, component by
//! component: core computes `let s := n.sqrt; if n - s * s < s then (n - s *
//! s, s) else (s, n - s * s - s)`. The two definitions below repeat the
//! shared `s` and `r` subterms rather than sharing a `let`, which costs
//! nothing at the kernel level (the terms are interned) and keeps each
//! definition a straight-line application of already-total primitives.
//!
//! # No recursion, no fuel, no termination argument
//!
//! Nothing here uses `Nat.rec`. `Nat.sqrt` supplies the only recursion and
//! it is already declared ([`sqrt.rs`](super::sqrt), structural fuel
//! recursion, axiom-free); `add`/`mul`/`sub`/`ble` are total primitives.
//! So there is no fuel argument, no absorbing-zero question, and no
//! argument-recursion order to get backwards.
//!
//! The strict order test reuses [`super::avg_pair`]'s reasoning: there is no
//! Bool `<` primitive, so [`blt`] is `ble (succ a) b`, definitionally
//! Mathlib's/Lean core's `Nat.blt` and matching this prelude's `Prop`-valued
//! `NatOps::lt` (`Nat.lt a b := Nat.le (succ a) b`) exactly.
//!
//! # What the kernel cannot tell you
//!
//! `Nat → Nat` is `Nat → Nat` whatever the body computes, so
//! `add_declaration` accepts a transposed branch, a projection that forgets
//! the `- s` correction, or the two projections swapped, exactly as happily
//! as the intended definition. Every check therefore lives in
//! `unpair_tests.rs` as a `def_eq` at concrete numerals against
//! independently hand-computed values.
//!
//! Two properties of that suite are load-bearing rather than decorative:
//!
//! - The **round trip against the already-declared `Nat.pair`** is the
//!   strongest available discriminator, because it ties this construction to
//!   a function whose own evaluation test already passed. A wrong branch
//!   here breaks the round trip at an argument pair the `pair` test already
//!   pins.
//! - The `unpaired` checks use an **asymmetric** `f`. A symmetric one
//!   (`add`, `mul`) cannot see swapped projections at all — the classic
//!   vacuous control — so `sub` is used, at an argument where the two
//!   orders give different values.
//!
//! Magnitudes are kept to single digits throughout. This prelude's numerals
//! are unary towers, so the kernel's binary literal fast path never fires,
//! and `Nat.sqrt n` is a linear search with `n` fuel: a large argument would
//! cost more than the whole prelude.
//!
//! No theorem about any of the three is declared here (ADR-0653: an
//! unblocking lane declares the construction and nothing else). The
//! round-trip identity `unpairLeft (pair a b) = a` is exactly the kind of
//! ordinary supporting theorem that belongs in a later lane, from
//! `development`, where it costs no blind-evaluation value.

use super::NatPrelude;
use super::ops::{NatDev, NatOps};
use crate::KernelError;
use crate::env::Declaration;
use crate::env::ReducibilityHint;
use crate::expr::ExprId;

/// Bool-valued `a < b`, i.e. `Nat.ble (succ a) b` — the executable
/// counterpart of `Nat.lt a b := Nat.le (succ a) b`. Same construction as
/// [`super::avg_pair`]'s, repeated rather than shared because that one is
/// module-private and this module wants no dependency on it beyond the
/// declared `Nat.pair` constant its tests use.
fn blt(d: &mut NatDev<'_>, a: ExprId, b: ExprId) -> ExprId {
    let sa = d.succ(a);
    d.ble(sa, b)
}

/// Declare `Nat.unpairLeft`, `Nat.unpairRight` and `Nat.unpaired`.
/// Definitions only — see this module's doc for why no theorem about any of
/// them is declared here.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_unpair_all(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();

    // --- Nat.unpairLeft n := if n - sqrt n * sqrt n < sqrt n
    //                         then n - sqrt n * sqrt n else sqrt n ---------
    {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);

        let s = d.const_app(p.sqrt, &[n]);
        let ss = d.mul(s, s);
        let r = d.sub(n, ss);
        let cond = blt(d, r, s);
        let body = d.bool_select_nat(cond, r, s);

        let value = d.lam_fv(n_fv, nat, body);
        let ty = d.arrow(nat, nat);
        d.kernel().add_declaration(Declaration::Definition {
            name: p.unpair_left,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(4),
        })?;
    }

    // --- Nat.unpairRight n := if n - sqrt n * sqrt n < sqrt n
    //                          then sqrt n else n - sqrt n * sqrt n - sqrt n
    {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);

        let s = d.const_app(p.sqrt, &[n]);
        let ss = d.mul(s, s);
        let r = d.sub(n, ss);
        let cond = blt(d, r, s);
        let on_false = d.sub(r, s);
        let body = d.bool_select_nat(cond, s, on_false);

        let value = d.lam_fv(n_fv, nat, body);
        let ty = d.arrow(nat, nat);
        d.kernel().add_declaration(Declaration::Definition {
            name: p.unpair_right,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(4),
        })?;
    }

    // --- Nat.unpaired f n := f (unpairLeft n) (unpairRight n) -------------
    {
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);

        let lhs = d.const_app(p.unpair_left, &[n]);
        let rhs = d.const_app(p.unpair_right, &[n]);
        let body = d.apply(f, &[lhs, rhs]);

        let binary = {
            let inner = d.arrow(nat, nat);
            d.arrow(nat, inner)
        };
        let value = {
            let with_n = d.lam_fv(n_fv, nat, body);
            d.lam_fv(f_fv, binary, with_n)
        };
        let ty = {
            let inner = d.arrow(nat, nat);
            d.arrow(binary, inner)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name: p.unpaired,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(5),
        })?;
    }

    Ok(())
}
