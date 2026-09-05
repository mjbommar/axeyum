//! Three rational inequalities whose proof terms are **searched for, never
//! written**: [`crate::psatz::rat::prove`] finds a sum-of-squares certificate
//! and emits the term, and the trusted gate admits it (ADR-1649).
//!
//! ## Why this file exists, and what makes it different from every other
//! `rat_prelude` module
//!
//! Every other declaration in this prelude has a proof a person wrote. These
//! three have a proof a *producer* found. There is no `&|d, v| { ... }` body
//! spelling out `sq_nonneg`, `add_nonneg` and the transports below — the
//! closure builds the STATEMENT and hands it to `psatz::rat::prove`, which
//! returns a term or declines. If the producer declines, the prelude does not
//! build; there is no hand-written fallback, deliberately, because a fallback
//! would make the "searched, not written" claim unfalsifiable.
//!
//! This is the flywheel's reconstruction arrow closing inside one crate: the
//! solver-side SOS route (`axeyum-solver`'s `reconstruct_sos_proof`) can refute
//! an asserted `p < 0`, and what it produces is a discharged contradiction; what
//! lands here is a THEOREM a library can cite.
//!
//! ## Where in the build order this has to sit
//!
//! Last, and not by preference. `psatz::rat` reads twelve `RatPrelude` fields
//! (`sq_nonneg`, `mul_nonneg`, `add_nonneg`, `add_le_add`, `le_refl`,
//! `add_zero`, `le_or_lt`, `le_of_lt`, `add_lt_add_of_le_of_lt`, `zero_add`,
//! `lt_of_le_of_lt`, `lt_irrefl`) and calls [`crate::ring::rat::prove_eq`],
//! which reads nine more. Every one of those must already be DECLARED in the
//! kernel, not merely interned, or the emitted term names a constant the
//! environment does not have. `laws`, `group` and `abs` are where those come
//! from, so this module runs after all of them.
//!
//! ## The three statements, and why these three
//!
//! | theorem | certificate | scale |
//! | --- | --- | --- |
//! | `Rat.two_mul_le_sq_add_sq : ∀ x y, (x·y) + (x·y) ≤ x·x + y·y` | `(x−y)²` | 1 |
//! | `Rat.mul_add_le_sq_add_sq_three : ∀ a b c, (a·b + b·c) + c·a ≤ (a·a + b·b) + c·c` | `(2a−b−c)² + 3(b−c)²` | **4** |
//! | `Rat.four_mul_le_sq_add : ∀ a b, ((a·b + a·b) + (a·b + a·b)) ≤ (a+b)·(a+b)` | `(a−b)²` | 1 |
//!
//! The middle one is the reason the producer has a denominator-clearing scale
//! at all: the Gram matrix of `a²+b²+c²−ab−bc−ca` has half-integer
//! off-diagonals, so **no** unit-weight integer-form decomposition of it
//! exists, and `4p = (2a−b−c)² + 3(b−c)²` is forced rather than chosen. The
//! third states the same mathematics as the first in the "squared means"
//! spelling, and is kept because its goal SHAPE is different — the right side
//! is a product of sums, so the parse has to distribute before a Gram matrix
//! exists at all.
//!
//! Coefficients are spelled as repeated addition (`(x·y) + (x·y)`, not
//! `2·(x·y)`) throughout, because `ring::rat` recognizes only the literals
//! `{-1, 0, 1}` and closes the certificate's identity through the additive
//! route; see [`crate::psatz`]'s module docs.

use crate::KernelError;
use crate::RatPrelude;
use crate::int_prelude::ops::IntDev;
use crate::psatz;
use crate::rat_prelude::ops::{radd, rat_theorem, rle, rmul};

/// Prove `goal` with the `psatz` producer, or turn its decline into a
/// [`KernelError`]-shaped failure of the prelude build.
///
/// The decline is *not* swallowed: a producer that stops finding these
/// certificates must break the build loudly, because the whole claim of this
/// module is that nothing here is hand-written. The panic carries the typed
/// decline so the failure names which of the producer's boundaries moved.
fn produced(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    label: &str,
    goal: crate::expr::ExprId,
) -> crate::expr::ExprId {
    let ctx = psatz::rat::Ctx {
        prelude: p,
        assumptions: &[],
        dual: None,
    };
    psatz::rat::prove(d, &ctx, goal).unwrap_or_else(|decline| {
        panic!(
            "psatz declined `{label}`: {decline:?} — this prelude has no \
             hand-written proof for it by design (ADR-1649), so a decline is a \
             build failure rather than a fallback"
        )
    })
}

/// Declare the three producer-proved inequalities.
///
/// # Errors
///
/// [`KernelError`] if the trusted gate refuses one of the emitted terms — which
/// is the outcome the producer's own tests deliberately provoke with a
/// corrupted certificate, and which must never happen for an honest one.
pub(super) fn declare_psatz_inequalities(
    d: &mut IntDev<'_>,
    p: RatPrelude,
) -> Result<(), KernelError> {
    // `(x·y) + (x·y) ≤ x·x + y·y` — the two-variable AM–GM. Certificate `(x−y)²`.
    rat_theorem(d, p.two_mul_le_sq_add_sq, 2, &|d, v| {
        let (x, y) = (v[0], v[1]);
        let xy = rmul(d, x, y);
        let lhs = radd(d, xy, xy);
        let xx = rmul(d, x, x);
        let yy = rmul(d, y, y);
        let rhs = radd(d, xx, yy);
        let goal = rle(d, p, lhs, rhs);
        let proof = produced(d, p, "Rat.two_mul_le_sq_add_sq", goal);
        (goal, proof)
    })?;

    // `(a·b + b·c) + c·a ≤ (a·a + b·b) + c·c` — the three-variable form.
    // Certificate `4p = (2a−b−c)² + 3(b−c)²`, so this is the one that exercises
    // the producer's `divide_by_scale`.
    rat_theorem(d, p.mul_add_le_sq_add_sq_three, 3, &|d, v| {
        let (a, b, c) = (v[0], v[1], v[2]);
        let ab = rmul(d, a, b);
        let bc = rmul(d, b, c);
        let ca = rmul(d, c, a);
        let products = radd(d, ab, bc);
        let lhs = radd(d, products, ca);
        let aa = rmul(d, a, a);
        let bb = rmul(d, b, b);
        let cc = rmul(d, c, c);
        let squares = radd(d, aa, bb);
        let rhs = radd(d, squares, cc);
        let goal = rle(d, p, lhs, rhs);
        let proof = produced(d, p, "Rat.mul_add_le_sq_add_sq_three", goal);
        (goal, proof)
    })?;

    // `((a·b + a·b) + (a·b + a·b)) ≤ (a+b)·(a+b)` — the squared-means spelling.
    // Certificate `(a−b)²`; the right side is a product of sums, so the parse
    // must distribute before a Gram matrix exists.
    rat_theorem(d, p.four_mul_le_sq_add, 2, &|d, v| {
        let (a, b) = (v[0], v[1]);
        let ab = rmul(d, a, b);
        let two_ab = radd(d, ab, ab);
        let lhs = radd(d, two_ab, two_ab);
        let sum = radd(d, a, b);
        let rhs = rmul(d, sum, sum);
        let goal = rle(d, p, lhs, rhs);
        let proof = produced(d, p, "Rat.four_mul_le_sq_add", goal);
        (goal, proof)
    })?;

    Ok(())
}
