//! `Nat.Abundant` and `Nat.Deficient` — open
//! `Mathlib.NumberTheory.FactorisationProperties` for the autogenesis screen.
//!
//! ADR-1100 (this lane). ADR-1095 measured why three consecutive draws
//! declined: `assign_partitions` assigns `held-out` only at cycle index
//! `0, 3, 6, …`, so `n` fresh families supply `ceil(n/3)` held-out ones and
//! R5's two-held-out minimum is unreachable below `n = 4`. Three families are
//! already constructible with no new work (`natural-avg-pair`,
//! `natural-minmax`, and a `Fib`/`Bitwise` combination), and every one of
//! them sorts EARLY by its first Mathlib module name — so the free supply
//! can fill cycle index 0 but never index 3. The fourth family has to be a
//! LATE-sorting, topically fresh one, and that is what these two definitions
//! buy: `Mathlib.NumberTheory.FactorisationProperties` sorts after every
//! free family, its module topic segment (`FactorisationProperties`) is
//! published by no development/train family, and its ten drawn rows are
//! R9-clean and R12-clean. Verified by SIMULATION against the real
//! `select()`/`guard()` before any of this was written, and re-screened
//! after — see the ADR.
//!
//! ## The definitions, and why they are not Mathlib's verbatim
//!
//! Mathlib states both against a sum over PROPER divisors:
//!
//! ```text
//! Nat.Abundant  n : Prop := n < ∑ i ∈ n.properDivisors, i
//! Nat.Deficient n : Prop := ∑ i ∈ n.properDivisors, i < n
//! ```
//!
//! This kernel has no `Finset`, so there is no `properDivisors` to sum over.
//! What it does have is `Nat.sumDivisors` (`perfect.rs`), the sum of EVERY
//! divisor in `[0,n]` including `n` itself, and `Nat.Perfect n :=
//! sumDivisors n = 2 * n` already states perfection in exactly that
//! subtraction-free form and for exactly that reason (`perfect.rs`'s module
//! doc: the proper-divisor phrasing needs `Nat.sub`, which truncates here and
//! would silently mask an off-by-one). So:
//!
//! ```text
//! Nat.Abundant  n := Lt (mul 2 n) (sumDivisors n)
//! Nat.Deficient n := Lt (sumDivisors n) (mul 2 n)
//! ```
//!
//! For `n ≥ 1`, `sumDivisors n = (∑ properDivisors n) + n`, so
//! `2n < sumDivisors n ↔ n < ∑ properDivisors n` — the same proposition,
//! stated without subtraction, and continuing `Nat.Perfect`'s own convention
//! so that the three predicates are comparable term-for-term (which is what
//! the module's trichotomy rows are about). At `n = 0` both sides are `0`,
//! so `Abundant 0` and `Deficient 0` are both `Lt 0 0`, i.e. false —
//! matching Mathlib, whose `properDivisors 0` is empty
//! (`Nat.not_abundant_zero` is one of the module's own rows).
//!
//! Per `CLAUDE.md`'s mirror-flip criterion this is the `Nat.minFac`/`Nat.nth`
//! case rather than the `Nat.descFactorial_of_lt` case: our definitional BODY
//! is provably equivalent to, and not definitionally identical with,
//! Mathlib's. Any `ml430` mirror stated against Mathlib's `Nat.Abundant`
//! therefore stays `open`, and a theorem about THIS predicate would need its
//! own `F:nat-*` fact.
//!
//! ## No theorems
//!
//! ADR-0653: an unblocking lane declares the construction and its evaluation
//! test and NOTHING else. A lane told to unblock `Nat.dist` also declared
//! seven ordinary supporting theorems, five of which carried exact Mathlib
//! mirror names in the same pool, and guard R9 correctly refused the whole
//! family as no longer blind. Every useful lemma about these two predicates
//! can land tomorrow from `development`, where it costs nothing.
//!
//! Neither definition uses `Nat.rec`: both are straight-line applications of
//! `Nat.sumDivisors`, `Nat.mul` and `Nat.lt`. There is no fuel argument, no
//! termination argument, and no recursion order to get backwards — the two
//! ways this kernel usually admits a wrong `Definition`. What CAN go wrong is
//! the direction of the `Lt` and the factor of two, and
//! `abundant_deficient_tests.rs` is a discriminating check for exactly those
//! (12 is abundant, 8 is deficient, 6 is neither).

use super::NatPrelude;
use super::ops::{NatDev, NatOps};
use crate::KernelError;
use crate::env::Declaration;
use crate::env::ReducibilityHint;

/// Declare `Nat.Abundant` and `Nat.Deficient`. Definitions only — see this
/// module's doc for why no theorem about either is declared here.
///
/// Must run after [`super::perfect::declare_perfect_all`], which declares
/// `Nat.sumDivisors`.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_abundant_deficient_all(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let prop = d.kernel().sort_zero();
    let ty = d.arrow(nat, prop);

    // --- Nat.Abundant n := Lt (mul 2 n) (sumDivisors n) ---------------------
    {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let sum = d.const_app(p.sum_divisors, &[n]);
        let two = d.num(2);
        let twice = d.mul(two, n);
        let body = d.lt(twice, sum);
        let value = d.lam_fv(n_fv, nat, body);
        d.kernel().add_declaration(Declaration::Definition {
            name: p.abundant,
            uparams: vec![],
            ty,
            value,
            // Strictly greater than `sum_divisors` (4), as `Nat.Perfect` is.
            hint: ReducibilityHint::Regular(5),
        })?;
    }

    // --- Nat.Deficient n := Lt (sumDivisors n) (mul 2 n) --------------------
    {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let sum = d.const_app(p.sum_divisors, &[n]);
        let two = d.num(2);
        let twice = d.mul(two, n);
        let body = d.lt(sum, twice);
        let value = d.lam_fv(n_fv, nat, body);
        d.kernel().add_declaration(Declaration::Definition {
            name: p.deficient,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(5),
        })?;
    }

    Ok(())
}
