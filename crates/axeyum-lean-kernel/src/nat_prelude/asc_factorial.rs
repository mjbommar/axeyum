//! `Nat.ascFactorial n k = n * (n+1) * … * (n+k-1)` (`k` factors), by
//! structural recursion on `k` — mirroring [`super::desc_factorial`] exactly,
//! but climbing with `Nat.add` instead of descending with truncated
//! `Nat.sub`:
//!
//! ```text
//! ascFactorial n zero     ≡ 1
//! ascFactorial n (succ k) ≡ (n + k) * ascFactorial n k
//! ```
//!
//! Mirrors Mathlib's `Nat.ascFactorial` (`Mathlib.Data.Nat.Factorial.Basic`):
//! `ascFactorial (n : ℕ) : ℕ → ℕ | 0 => 1 | k + 1 => (n + k) * ascFactorial n k`.
//! Structural in `k`, built with the same [`NatOps::define_binary`]
//! combinator `Nat.sub`/`Nat.mul`/`Nat.descFactorial` already use for a
//! two-argument, second-argument recursion — so
//! [`declare_asc_factorial`]'s two equation theorems hold by `Eq.refl`
//! (β/δ/ι), no fuel device needed.
//!
//! Unlike `descFactorial`, `Nat.add` never truncates, so there is no
//! analogue of `descFactorial_of_lt`'s zero boundary here — `ascFactorial`
//! is `0` only when `n = 0` and `k ≥ 1` (Mathlib's `Nat.zero_ascFactorial`),
//! which this module does not prove. [`declare_asc_factorial_one`] is the
//! boundary lemma this slice lands, mirroring
//! [`super::desc_factorial::declare_desc_factorial_one`] exactly: `n *
//! ascFactorial n 1` reduces to `n * 1` by pure β/δ/ι, and `Nat.mul_one`
//! closes it directly.
//!
//! Evaluation test (`nat_prelude_tests::asc_factorial_evaluates_correctly`):
//! `ascFactorial 3 2 = 3 * 4 = 12`, `ascFactorial 5 0 = 1`, with a negative
//! control that a *descending* product (`5 * 4 = 20`, i.e. `descFactorial`'s
//! answer) is a DIFFERENT value — catching a copy-paste that reused `sub`
//! instead of `add` in the step function, which would still type-check
//! (`Nat → Nat → Nat` either way) but compute the wrong value.

use super::NatPrelude;
use super::ops::{NatDev, NatOps};
use crate::KernelError;
use crate::expr::ExprId;

/// `Nat.ascFactorial n k`.
fn asc_factorial(d: &mut NatDev<'_>, p: &NatPrelude, n: ExprId, k: ExprId) -> ExprId {
    d.const_app(p.asc_factorial, &[n, k])
}

/// `Nat.ascFactorial : Nat → Nat → Nat`, structural recursion on the
/// **second** argument via [`NatOps::define_binary`] — the same combinator
/// [`super::desc_factorial::declare_desc_factorial`] uses — so
/// `ascFactorial_zero`/`ascFactorial_succ` below hold by `Eq.refl` (β/δ/ι)
/// and exist only so callers can rewrite by name.
pub(super) fn declare_asc_factorial(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    // ascFactorial n zero ≡ 1 ; ascFactorial n (succ k) ≡ (n + k) * ascFactorial n k
    d.define_binary(p.asc_factorial, 3, &|d, _n| d.num(1), &|d, n, k, ih| {
        let n_plus_k = d.add(n, k);
        d.mul(n_plus_k, ih)
    })?;

    // ascFactorial_zero : ∀ n, n.ascFactorial 0 = 1
    d.theorem(p.asc_factorial_zero, 1, &|d, v| {
        let n = v[0];
        let zero = d.zero();
        let lhs = asc_factorial(d, &p, n, zero);
        let one = d.num(1);
        (d.eq(lhs, one), d.refl(one))
    })?;

    // ascFactorial_succ : ∀ n k, n.ascFactorial (succ k) = (n + k) * n.ascFactorial k
    d.theorem(p.asc_factorial_succ, 2, &|d, v| {
        let (n, k) = (v[0], v[1]);
        let sk = d.succ(k);
        let lhs = asc_factorial(d, &p, n, sk);
        let prior = asc_factorial(d, &p, n, k);
        let n_plus_k = d.add(n, k);
        let rhs = d.mul(n_plus_k, prior);
        (d.eq(lhs, rhs), d.refl(rhs))
    })?;

    Ok(())
}

/// `ascFactorial_one : ∀ n, n.ascFactorial 1 = n`.
///
/// `n.ascFactorial 1` reduces (`ascFactorial_succ` at `k := 0`,
/// definitionally) to `(n + 0) * n.ascFactorial 0`, and `n + 0 ≡ n` is
/// itself definitional (`Nat.add`'s own base case, right-recursive, holds
/// for any `n`). So the stated goal is defeq to `n * 1 = n`, and
/// `mul_one`'s own proof term closes it directly — no explicit rewrite
/// needed, exactly mirroring
/// [`super::desc_factorial::declare_desc_factorial_one`].
pub(super) fn declare_asc_factorial_one(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.asc_factorial_one, 1, &|d, v| {
        let n = v[0];
        let one = d.num(1);
        let lhs = asc_factorial(d, &p, n, one);
        let proof = d.lemma(p.mul_one, &[n]);
        (d.eq(lhs, n), proof)
    })?;
    Ok(())
}

/// Declare [`declare_asc_factorial`], then [`declare_asc_factorial_one`],
/// which depends only on `Nat.mul_one`, declared far earlier in the prelude
/// build.
pub(super) fn declare_asc_factorial_all(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    declare_asc_factorial(d, p)?;
    declare_asc_factorial_one(d, p)?;
    Ok(())
}
