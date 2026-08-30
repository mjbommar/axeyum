//! `Nat.log2` — the Lean **core** binary logarithm
//! (`Init/Data/Nat/Log2.lean`), NOT a Mathlib definition. Mathlib imports it
//! unchanged and states `Nat.log2_eq_log_two` about it
//! (`Mathlib/Data/Nat/Log.lean`).
//!
//! Read directly from the pinned toolchain source
//! (`leanprover/lean4` `v4.30.0`, the same pin `scripts/check-lean-gate.sh`
//! resolves), Lean core's own definition is
//!
//! ```text
//! def log2 (n : Nat) : Nat :=
//!   n.rec (fun _ => nat_lit 0)
//!         (fun _ ih n => ((nat_lit 2).ble n).rec (nat_lit 0) ((ih (n.div (nat_lit 2))).succ))
//!         n
//!
//! theorem log2_def (n : Nat) : n.log2 = if 2 ≤ n then (n / 2).log2 + 1 else 0
//! ```
//!
//! This is a **fuel-recursive `Nat.rec` with a non-dependent motive
//! `fun _ => Nat -> Nat`, fuel = the value itself (diagonal), single guard
//! `2 ≤ n`** — precisely [`log.rs`](super::log)'s own device (fuel argument
//! second, motive the constant row `fun _ => Nat -> Nat`), specialized to
//! the *literal* base `2`. `logAux`'s recursive step is
//!
//! ```text
//! logAux b (succ f) n ≡ if b ≤ n then (if 2 ≤ b then succ (logAux b f (n / b)) else 0) else 0
//! ```
//!
//! and at `b := 2` the INNER cut `2 ≤ b` becomes `2 ≤ 2`, a literal-literal
//! `Nat.ble` comparison that reduces to `Bool.true` by ι alone — independent
//! of the (possibly symbolic) fuel `f` or value `n` — collapsing the whole
//! guard to the single OUTER cut `2 ≤ n`. That is Lean core's `log2_def`
//! equation, verbatim, and it was checked against `log2`'s own doc-comment
//! examples before writing any of this file: `log(2,0)=0`, `log(2,1)=0`
//! (both `n < 2`), `log(2,2)=1`, `log(2,4)=2`, `log(2,7)=2`, `log(2,8)=3` —
//! all six agree with `Nat.log2`'s worked examples.
//!
//! So `Nat.log2` and `Nat.log 2` are not merely equal, they are the SAME
//! recursion at the same fixed base — the honest side of the mirror-flip
//! criterion (`CLAUDE.md`): Lean core *defines* `log2` this way; it is not a
//! *theorem* about a structurally different `def`. Accordingly `Nat.log2` is
//! declared here as `fun n => Nat.log 2 n` directly, rather than re-deriving
//! a second, independent fuel recursor, which makes
//! [`log2_eq_log_two`](NatPrelude::log2_eq_log_two) a one-line `Eq.refl`.
//! Mathlib's own proof of the same statement (`Mathlib/Data/Nat/Log.lean`)
//! is NOT this short — its `Nat.log` is well-founded recursion, a genuinely
//! different recursion principle from its `log2`, so it goes through
//! `eq_of_forall_le_iff` plus `le_log2`/`le_log_iff_pow_le`. This prelude's
//! `Nat.log` is already fuel-recursive at every base, so the two collapse to
//! the identical term by construction and no such argument is needed.

use super::NatPrelude;
use super::ops::{NatDev, NatOps};
use crate::KernelError;
use crate::env::Declaration;
use crate::env::ReducibilityHint;
use crate::expr::ExprId;

/// `Nat.log2 n`.
fn log2(d: &mut NatDev<'_>, p: &NatPrelude, n: ExprId) -> ExprId {
    d.const_app(p.log2, &[n])
}

/// Declare `Nat.log2` and `Nat.log2_eq_log_two`.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_log2_all(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();

    // --- Nat.log2 : Nat -> Nat -----------------------------------------------
    {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let two = d.num(2);
        let body = d.const_app(p.log, &[two, n]);
        let value = d.lam_fv(n_fv, nat, body);
        let ty = d.arrow(nat, nat);
        d.kernel().add_declaration(Declaration::Definition {
            name: p.log2,
            uparams: vec![],
            ty,
            // Strictly greater than `Nat.log`'s height (5), the only
            // definition this body calls.
            value,
            hint: ReducibilityHint::Regular(6),
        })?;
    }

    // log2_eq_log_two : ∀ n, Eq (log2 n) (log 2 n) -- refl, per the module
    // doc: `log2 n` delta-unfolds directly to `log 2 n`.
    d.theorem(p.log2_eq_log_two, 1, &|d, values| {
        let n = values[0];
        let two = d.num(2);
        let lhs = log2(d, &p, n);
        let rhs = d.const_app(p.log, &[two, n]);
        let stmt = d.eq(lhs, rhs);
        let proof = d.refl(lhs);
        (stmt, proof)
    })?;

    Ok(())
}
