//! `Nat.xor` — bitwise XOR, defined directly as a specialization of the
//! already-general [`NatPrelude::bitwise`](super::NatPrelude::bitwise)
//! (`bitwise.rs`) rather than as a fourth hand-rolled fuel recursion.
//! Mathlib v4.30 (`Mathlib.Data.Nat.Bitwise`) defines `Nat.xor := bitwise
//! xor`, so this lands the SAME shape as the upstream definition, not
//! merely something pointwise-equal to it — exactly the alternative
//! `bitwise.rs`'s own module doc flags as available and unexplored
//! ("no prelude XOR sibling exists").
//!
//! `bitwise.rs` already builds [`xor_fn`](super::bitwise::xor_fn) (`fun a b
//! => bool_select_bool a (bool_select_bool b false true) b`, i.e.
//! `Bool.xor`) purely to instantiate `bitwise`'s `f` slot for
//! `bitwise_xor_three_five` (`Eq (bitwise xor_fn 3 5) 6`). This file reuses
//! that exact term as the VALUE of a genuine top-level `Nat.xor`
//! definition, so `xor 3 5` reduces to `6` by the identical computation
//! `bitwise_xor_three_five` already checks — no new per-bit reasoning, no
//! new height dependency beyond `bitwise` itself, and no fourth
//! `bitwiseAux`-shaped recursion to get right or wrong.
//!
//! # The absorbing-zero question is moot here
//!
//! The CLAUDE.md bitwise-family rule — "does the FUEL operand carry this
//! operator's absorbing zero?" — governs a hand-written fuel-exhaustion
//! *row*. `xor` never writes one: it is a direct partial application of
//! `bitwise`, so it inherits `bitwise`'s already-proved, `f`-general
//! boundary theorems
//! ([`bitwise_zero_left`](super::NatPrelude::bitwise_zero_left),
//! [`bitwise_zero_right`](super::NatPrelude::bitwise_zero_right)) rather
//! than needing new ones. For the record, since the rule is worth checking
//! even when it is not needed: XOR is `lor`-shaped, not `land`-shaped
//! (`0 XOR n = n`, so the fuel operand does *not* carry XOR's absorbing
//! identity), and `bitwise_aux`'s general fuel-exhaustion row
//! (`if f false true then n else 0`) reproduces exactly that by δβι alone
//! at `f = xor_fn`: `xor false true` reduces to `true`, so the row returns
//! `n` — the same derivation `bitwise.rs`'s module doc gives for `lor`.
//!
//! # Closing `F:ml430-nat-even-xor-…` / `F:ml430-nat-lt-xor-cases-…`
//!
//! Both facts stay open. Neither is in reach from what this file adds:
//!
//! - `Nat.even_xor` needs a bridge from `Even`/`Odd`
//!   ([`parity.rs`](super::parity), an existential `∃ k, n = k+k` predicate
//!   family with no established connection to `Nat.mod _ 2` anywhere in
//!   this prelude) to the LOW BIT of a `bitwise`-family value. That bit is
//!   only exposed one `bitwiseAux` fuel-step down
//!   (`bitwise_aux`'s `succ_minor` row's `combined_nat` term in
//!   `bitwise.rs`), conditioned on `m`/`n` both being nonzero — the `m = 0`
//!   / `n = 0` cases return an *operand itself*, not a per-bit combine, so
//!   the general statement needs its own case split before the per-bit
//!   argument even applies. That is new machinery, not a corollary of
//!   `Nat.xor`'s definition.
//! - `Nat.lt_xor_cases` is a highest-differing-bit argument (Mathlib's own
//!   proof inducts on `Nat.testBit` disagreement) with no existing lemma
//!   in this prelude to build from; it is unrelated in size to defining
//!   `xor` itself.
//!
//! Landing `Nat.xor` with a discriminating evaluation test, with neither
//! fact closed, is recorded here as the deliverable — see
//! `docs/plan/status/253-nat-xor-parity.md`.

use super::NatPrelude;
use super::bitwise::xor_fn;
use super::ops::NatDev;
use crate::KernelError;
use crate::env::Declaration;
use crate::env::ReducibilityHint;

/// Declare `Nat.xor := bitwise xor_fn` and one discriminating evaluation
/// check.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_xor_all(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let nat_to_nat = d.arrow(nat, nat);
    let ty = d.arrow(nat, nat_to_nat);

    // --- Nat.xor := Nat.bitwise xor_fn --------------------------------------
    {
        let xor_ = xor_fn(d);
        let value = d.const_app(p.bitwise, &[xor_]);
        d.kernel().add_declaration(Declaration::Definition {
            name: p.xor,
            uparams: vec![],
            ty,
            // Strictly greater than `bitwise`'s height (5): this is a
            // direct partial application of an already-declared
            // definition, not a new recursion, so no new height
            // dependency beyond one more than what it calls.
            value,
            hint: ReducibilityHint::Regular(6),
        })?;
    }

    // xor_three_five : Eq (xor 3 5) 6 -- refl, the identical reduction
    // `bitwise_xor_three_five` already checks, now against the public
    // `Nat.xor` name rather than an inline `xor_fn` application. Chosen to
    // DISCRIMINATE against every sibling operator at the same operand pair
    // (3, 5): land = 1, lor = 7, ldiff = 2 (ldiff 5 3 = 4), xor = 6 -- five
    // distinct numerals, so a copy-paste of any neighbour's proof fails
    // loudly instead of passing.
    {
        let three = d.num(3);
        let five = d.num(5);
        let six = d.num(6);
        let lhs = d.const_app(p.xor, &[three, five]);
        let stmt = d.eq(lhs, six);
        let proof = d.refl(lhs);
        d.kernel().add_declaration(Declaration::Theorem {
            name: p.xor_three_five,
            uparams: vec![],
            ty: stmt,
            value: proof,
        })?;
    }

    Ok(())
}
