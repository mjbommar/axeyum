//! `Nat.sqrt` — the floor square root, by **structural fuel recursion**.
//!
//! Mathlib v4.30 (`Init.Data.Nat.Basic`) defines `Nat.sqrt` by a
//! well-founded Newton's-method iteration:
//!
//! ```text
//! def sqrt (n : Nat) : Nat :=
//!   if n ≤ 1 then n else iter n (n / 2)
//! where
//!   iter (n guess : Nat) : Nat :=
//!     let next := (guess + n / guess) / 2
//!     if next < guess then iter n next else guess
//!   termination_by guess
//! ```
//!
//! Convergence of `iter` is not a constructor-predecessor recursion — Lean
//! discharges it with `WellFounded.fix`, and through the equation compiler
//! that drags in `Quot.sound`/`propext`, fatal to this project's
//! axiom-freedom metric ([`log.rs`](super::log) hit the identical problem for
//! `Nat.log` and is the template this file follows).
//!
//! This file does **not** reproduce Newton's method. It computes the same
//! *value* — `Nat.sqrt n` is characterized by Mathlib's own
//! `Nat.sqrt_le' : sqrt n * sqrt n ≤ n` and `Nat.lt_succ_sqrt' : n < succ
//! (sqrt n) * succ (sqrt n)`, i.e. `sqrt n` is the greatest `m` with `m * m ≤
//! n` — by **linear search upward**, structurally recursing on a **fuel**
//! argument exactly as [`declare_executable_division`](super::defs)　and
//! [`declare_log_all`](super::log) do:
//!
//! ```text
//! Nat.sqrtAux n 0        ≡ 0
//! Nat.sqrtAux n (succ f) ≡ let c := Nat.sqrtAux n f
//!                          in if succ c * succ c ≤ n then succ c else c
//! Nat.sqrt n             := Nat.sqrtAux n n
//! ```
//!
//! Both equations hold **definitionally** (β/δ/ι), so no equation lemmas are
//! needed and nothing here appeals to an axiom.
//!
//! `n` always suffices as fuel: the accumulator starts at `0` and increments
//! by at most `1` per fuel step, and the greatest `m` with `m * m ≤ n` is
//! itself `≤ n` (equality only at `n ∈ {0, 1}`), so at most `n` increments
//! are ever needed. Unlike [`log_aux`](super::log), the target `n` is **not**
//! threaded through `Nat.rec`'s motive at all — it is a free variable
//! captured by the whole term and abstracted only once, at the very end, so
//! the motive is the plain `fun _ => Nat` (an accumulator fold), simpler than
//! `logAux`'s `fun _ => Nat → Nat` (which needed a function there because
//! `log`'s recursive argument, `n / b`, genuinely changes per fuel level).
//!
//! `sqrt_zero` (`sqrt 0 = 0`) and `sqrt_one` (`sqrt 1 = 1`) are **both**
//! fully concrete instantiations — no free variable survives past the two
//! literal arguments — so both close by a single `refl`, no induction
//! needed. They are simultaneously the `n ∈ {0, 1}` instances of Mathlib's
//! general `Nat.sqrt_eq (n) : sqrt (n * n) = n` (open here as
//! `F:ml430-nat-sqrt-eq-79ae8eae`, since `0 * 0 ≡ 0` and `1 * 1 ≡ 1`
//! definitionally): the cases of that family that reduce by `refl` alone,
//! landed as the two boundary theorems below rather than restated in the
//! `n * n` shape. The general theorem is **not** claimed here — it needs an
//! inductive argument that the linear search never overshoots, which this
//! file does not attempt.

use super::NatPrelude;
use super::ops::{NatDev, NatOps};
use crate::BinderInfo;
use crate::KernelError;
use crate::env::Declaration;
use crate::env::ReducibilityHint;
use crate::expr::ExprId;

/// `Nat.sqrtAux value fuel`.
fn sqrt_aux(d: &mut NatDev<'_>, p: &NatPrelude, value: ExprId, fuel: ExprId) -> ExprId {
    d.const_app(p.sqrt_aux, &[value, fuel])
}

/// `Nat.sqrt value`.
fn sqrt(d: &mut NatDev<'_>, p: &NatPrelude, value: ExprId) -> ExprId {
    d.const_app(p.sqrt, &[value])
}

/// Declare `Nat.sqrtAux`, `Nat.sqrt`, and the two boundary equations that
/// fall out of the definition by ι-reduction alone.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_sqrt_all(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let anon = d.anon_name();
    let level_one = d.level_one();

    // --- Nat.sqrtAux : Nat -> Nat -> Nat ------------------------------------
    {
        let value_fv = d.fresh_fvar();
        let value = d.kernel().fvar(value_fv);
        let fuel_fv = d.fresh_fvar();
        let fuel = d.kernel().fvar(fuel_fv);

        // fuel = zero: the accumulator starts at 0.
        let zero_minor = d.zero();

        // fuel = succ f: one linear-search step. `predecessor` (the shrunk
        // fuel) is unused -- only the running accumulator `ih` matters, so
        // this is a plain fold, not (like `logAux`) a function-valued one.
        let succ_minor = {
            let predecessor_fv = d.fresh_fvar();
            let accumulator_fv = d.fresh_fvar();
            let accumulator = d.kernel().fvar(accumulator_fv);
            let candidate = d.succ(accumulator);
            let candidate_sq = d.mul(candidate, candidate);
            let fits = d.ble(candidate_sq, value);
            let body = d.bool_select_nat(fits, candidate, accumulator);
            let with_accumulator = d.lam_fv(accumulator_fv, nat, body);
            d.lam_fv(predecessor_fv, nat, with_accumulator)
        };

        let motive = d.kernel().lam(anon, nat, nat, BinderInfo::Default);
        let rec = d.kernel().const_(p.rec, vec![level_one]);
        let applied = d.apply(rec, &[motive, zero_minor, succ_minor, fuel]);
        let value_term = {
            let with_fuel = d.lam_fv(fuel_fv, nat, applied);
            d.lam_fv(value_fv, nat, with_fuel)
        };
        let ty = {
            let inner = d.arrow(nat, nat);
            d.arrow(nat, inner)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name: p.sqrt_aux,
            uparams: vec![],
            ty,
            value: value_term,
            hint: ReducibilityHint::Regular(4),
        })?;
    }

    // --- Nat.sqrt n := Nat.sqrtAux n n --------------------------------------
    {
        let value_fv = d.fresh_fvar();
        let value = d.kernel().fvar(value_fv);
        let body = sqrt_aux(d, &p, value, value);
        let value_term = d.lam_fv(value_fv, nat, body);
        let ty = d.arrow(nat, nat);
        d.kernel().add_declaration(Declaration::Definition {
            name: p.sqrt,
            uparams: vec![],
            ty,
            value: value_term,
            hint: ReducibilityHint::Regular(5),
        })?;
    }

    // sqrt 0 = 0 -- fuel is already exhausted, so this is pure ι.
    d.theorem(p.sqrt_zero, 0, &|d, _values| {
        let zero = d.zero();
        let lhs = sqrt(d, &p, zero);
        (d.eq(lhs, zero), d.refl(lhs))
    })?;

    // sqrt 1 = 1 -- fully concrete: one fuel step finds `1 * 1 <= 1`.
    d.theorem(p.sqrt_one, 0, &|d, _values| {
        let one = d.num(1);
        let lhs = sqrt(d, &p, one);
        (d.eq(lhs, one), d.refl(lhs))
    })?;

    Ok(())
}
