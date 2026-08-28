//! `Nat.bit` — append a bit to the little end of a binary numeral.
//!
//! Mathlib v4.30 (`Mathlib.Data.Nat.Bitwise`) defines
//!
//! ```text
//! def bit (b : Bool) (n : ℕ) : ℕ := cond b (2 * n + 1) (2 * n)
//! ```
//!
//! Unlike [`log`](super::log), [`sqrt`](super::sqrt), and [`clog`](super::clog),
//! `Nat.bit` needs **no fuel device at all**. Those three definitions are not
//! structural — the recursive call is at a strictly smaller argument that is
//! not a constructor predecessor — and fuel is how this prelude discharges
//! that without dragging in `WellFounded`/`Quot.sound`/`propext`. `Nat.bit` has
//! no recursive call to justify in the first place: it is a single case split
//! on its `Bool` argument, computing one of two closed forms of `n`. So it is
//! declared as an ordinary non-recursive lambda, exactly the shape `Nat.bit`
//! already has in Mathlib.
//!
//! This file states it as
//!
//! ```text
//! Nat.bit b n := Nat.add (Nat.mul 2 n) (cond b 1 0)
//! ```
//!
//! rather than Mathlib's `cond`-outermost `cond b (2*n+1) (2*n)`. The two are
//! *not* the same term, but they normalize to the same value at every literal
//! `b`, which is all any boundary theorem below needs:
//!
//! - `bit false n`: `cond false 1 0 ≡ 0` (ι, on the inner `Bool.rec`), and then
//!   `Nat.add`'s own zero case (`add x zero ≡ x`, ι again) collapses the whole
//!   term to `2 * n`.
//! - `bit true n`: `cond true 1 0 ≡ 1 = succ zero`, and then `Nat.add`'s
//!   successor case (`add x (succ j) ≡ succ (add x j)`) collapses the term to
//!   `succ (2 * n)` — the same normal form `Nat.add (2 * n) 1` itself reduces
//!   to, which is why [`bit_true`](NatPrelude::bit_true) can state the RHS as
//!   `add (mul 2 n) 1` (the more legible "2n+1") and still close by `refl`.
//!
//! Choosing the `add`-outermost form buys more than legibility: it makes
//! [`bit_true_pos`](NatPrelude::bit_true_pos) and
//! [`bit_false_le_bit_true`](NatPrelude::bit_false_le_bit_true) **defeq
//! corollaries of already-proved generic order lemmas** (`zero_lt_succ`,
//! `le_succ`) instantiated at `mul 2 n`, with no case-split combinator and no
//! induction — the kernel's own definitional-equality check does the work of
//! unfolding `bit` down to `succ (mul 2 n)` (or `mul 2 n`) and matching it
//! against the generic lemma's conclusion. Mathlib's `cond`-outermost form
//! would need the same case split `log.rs`'s `le_of_bool_select` performs by
//! hand for exactly the same lemmas.

use super::NatPrelude;
use super::ops::{NatDev, NatOps};
use crate::KernelError;
use crate::env::Declaration;
use crate::env::ReducibilityHint;
use crate::expr::ExprId;

/// `Nat.bit test n`.
fn bit(d: &mut NatDev<'_>, p: &NatPrelude, test: ExprId, n: ExprId) -> ExprId {
    d.const_app(p.bit, &[test, n])
}

/// Declare `Nat.bit` and its boundary theorems.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_bit_all(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let bool_ty = d.bool_ty();

    // --- Nat.bit : Bool -> Nat -> Nat ---------------------------------------
    {
        let test_fv = d.fresh_fvar();
        let test = d.kernel().fvar(test_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);

        let two = d.num(2);
        let one = d.num(1);
        let zero = d.zero();
        let doubled = d.mul(two, n);
        let selected = d.bool_select_nat(test, one, zero);
        let body = d.add(doubled, selected);

        let value = {
            let with_n = d.lam_fv(n_fv, nat, body);
            d.lam_fv(test_fv, bool_ty, with_n)
        };
        let ty = {
            let inner = d.arrow(nat, nat);
            d.arrow(bool_ty, inner)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name: p.bit,
            uparams: vec![],
            ty,
            // Strictly greater than `Nat.mul`'s height (2), which is the
            // higher of the two definitions this body calls (`Nat.add` is 1).
            value,
            hint: ReducibilityHint::Regular(3),
        })?;
    }

    // bit_false : ∀ n, Eq (bit false n) (mul 2 n) -- refl, per the module doc.
    d.theorem(p.bit_false, 1, &|d, values| {
        let n = values[0];
        let false_ = d.bool_false();
        let two = d.num(2);
        let lhs = bit(d, &p, false_, n);
        let rhs = d.mul(two, n);
        let stmt = d.eq(lhs, rhs);
        let proof = d.refl(lhs);
        (stmt, proof)
    })?;

    // bit_true : ∀ n, Eq (bit true n) (add (mul 2 n) 1) -- refl, per the
    // module doc: both sides reduce to `succ (mul 2 n)`.
    d.theorem(p.bit_true, 1, &|d, values| {
        let n = values[0];
        let true_ = d.bool_true();
        let two = d.num(2);
        let one = d.num(1);
        let lhs = bit(d, &p, true_, n);
        let doubled = d.mul(two, n);
        let rhs = d.add(doubled, one);
        let stmt = d.eq(lhs, rhs);
        let proof = d.refl(lhs);
        (stmt, proof)
    })?;

    // bit_true_pos : ∀ n, Lt 0 (bit true n) -- `bit true n` unfolds
    // (delta+iota) to `succ (mul 2 n)`, so `zero_lt_succ` at `mul 2 n` is
    // accepted directly by defeq against the declared statement.
    d.theorem(p.bit_true_pos, 1, &|d, values| {
        let n = values[0];
        let true_ = d.bool_true();
        let two = d.num(2);
        let doubled = d.mul(two, n);
        let proof = d.zero_lt_succ(doubled);
        let zero = d.zero();
        let lhs = bit(d, &p, true_, n);
        let stmt = d.lt(zero, lhs);
        (stmt, proof)
    })?;

    // bit_false_le_bit_true : ∀ n, Le (bit false n) (bit true n) -- both sides
    // unfold to `mul 2 n` and `succ (mul 2 n)`, so `le_succ` at `mul 2 n` is
    // accepted directly by defeq against the declared statement.
    d.theorem(p.bit_false_le_bit_true, 1, &|d, values| {
        let n = values[0];
        let false_ = d.bool_false();
        let true_ = d.bool_true();
        let two = d.num(2);
        let doubled = d.mul(two, n);
        let proof = d.lemma(p.le_succ, &[doubled]);
        let lhs = bit(d, &p, false_, n);
        let rhs = bit(d, &p, true_, n);
        let stmt = d.le(lhs, rhs);
        (stmt, proof)
    })?;

    Ok(())
}
