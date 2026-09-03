//! `decide` over ℤ — the ℕ fragment's design ([`super`]'s module docs),
//! extended to `Int`'s two-constructor shape.
//!
//! `Int.le`/`Int.lt` are FOUR-CASE DEFINITIONS over `Nat.le`/`Nat.lt`
//! (`int_prelude::defs`'s own module docs carry the table), not a second
//! inductive relation the way `Nat.le` is — so this producer's job is not
//! "build a `le_step` chain" a second time, it is "peel BOTH operands to
//! their `(constructor, magnitude)` shape, and select which of the four
//! `Nat`-level facts (or `True`/`False`) the case reduces to":
//!
//! | `a` | `b` | `Int.le a b` reduces to | witness |
//! | --- | --- | --- | --- |
//! | `ofNat m` | `ofNat n` | `Nat.le m n` | [`super::le_witness`] |
//! | `ofNat m` | `negSucc n` | `False` | none — [`Decline::Undecidable`] |
//! | `negSucc m` | `ofNat n` | `True` | [`IntDev::true_intro`] |
//! | `negSucc m` | `negSucc n` | `Nat.le n m` | [`super::le_witness`], reversed |
//!
//! `Int.lt` has the identical shape over `Nat.lt` — and since `Nat.lt a b`
//! is ITSELF definitionally `Nat.le (succ a) b` (`super`'s own module docs),
//! its witness is the exact same [`super::le_witness`] call with the first
//! magnitude incremented, relying on the kernel's `def_eq` to bridge
//! `Int.lt a b`'s reduct down to that `Nat.le` application — no separate
//! "Lt witness" builder, mirroring [`super::run`]'s own `Shape::Lt` case
//! exactly.
//!
//! Every witness below is built at the REDUCED type (`Nat.le`/`Nat.lt`/
//! `True`) and ascribed against the ORIGINAL `Int.le`/`Int.lt`/`Eq Int`
//! goal — the kernel's own `def_eq`, not this producer, is what confirms
//! `Int.le a b` (a `Definition` application) really does reduce to that
//! term, exactly the trick every other producer in this crate already
//! relies on for a definitional identity.

use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::int_prelude::ops::Shape as IntShape;
use crate::nat_prelude::NatOps;

use super::{Decline, Shape, head_const, is_closed, le_witness, nat_value, spine};

/// Parse `goal` as `Eq Int lhs rhs`, `Int.le lhs rhs`, or `Int.lt lhs rhs`.
#[cfg_attr(not(test), allow(dead_code))]
fn parse_goal(d: &mut IntDev<'_>, e: ExprId) -> Option<(Shape, ExprId, ExprId)> {
    let (head, args) = spine(d, e);
    let name = head_const(d, head)?;
    let p = d.int();
    let int_ty = d.int_ty();
    if name == p.logic.eq && args.len() == 3 && args[0] == int_ty {
        return Some((Shape::Eq, args[1], args[2]));
    }
    if name == p.le && args.len() == 2 {
        return Some((Shape::Le, args[0], args[1]));
    }
    if name == p.lt && args.len() == 2 {
        return Some((Shape::Lt, args[0], args[1]));
    }
    None
}

/// Peel `e` (already known closed) down to `(constructor, magnitude)`: `whnf`,
/// require the head to be `Int.ofNat`/`Int.negSucc`, and peel the `Nat`
/// argument via [`super::nat_value`] (reused directly — `IntDev` implements
/// [`NatOps`] over the SAME embedded `Nat` prelude `Int` is built on, so a
/// `succ`/`zero` chain or the kernel's compact `Lit` -- either -- peels
/// exactly as it does for a bare `Nat` goal).
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) fn int_value(d: &mut IntDev<'_>, e: ExprId) -> Result<(IntShape, u32), Decline> {
    let w = d.kernel().whnf(e);
    let (head, args) = spine(d, w);
    let name = head_const(d, head).ok_or(Decline::Undecidable)?;
    let p = d.int();
    let nat_prelude = p.nat;
    if name == p.of_nat && args.len() == 1 {
        let mag = nat_value(d, &nat_prelude, args[0])?;
        return Ok((IntShape::OfNat, mag));
    }
    if name == p.neg_succ && args.len() == 1 {
        let mag = nat_value(d, &nat_prelude, args[0])?;
        return Ok((IntShape::NegSucc, mag));
    }
    Err(Decline::Undecidable)
}

/// Prove `goal`, a closed `Eq Int`, `Int.le`, or `Int.lt` proposition, by
/// kernel reduction, or decline.
///
/// # Errors
///
/// [`Decline::NotClosed`] on a free variable, [`Decline::GoalNotAtomic`] on
/// an unrecognised shape, [`Decline::Undecidable`] when reduction does not
/// settle within [`super::MAX_MAGNITUDE`], the two sides genuinely disagree,
/// or (for `Int.le`/`Int.lt`) the case is the one that reduces to `False`.
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) fn run(d: &mut IntDev<'_>, goal: ExprId) -> Result<ExprId, Decline> {
    if !is_closed(d, goal) {
        return Err(Decline::NotClosed);
    }
    let (shape, lhs, rhs) = parse_goal(d, goal).ok_or(Decline::GoalNotAtomic)?;
    let (shape_a, mag_a) = int_value(d, lhs)?;
    let (shape_b, mag_b) = int_value(d, rhs)?;

    match shape {
        Shape::Eq => {
            if shape_a == shape_b && mag_a == mag_b {
                Ok(d.irefl(lhs))
            } else {
                Err(Decline::Undecidable)
            }
        }
        Shape::Le => match (shape_a, shape_b) {
            (IntShape::OfNat, IntShape::OfNat) => {
                if mag_a > mag_b {
                    return Err(Decline::Undecidable);
                }
                let nat_prelude = d.int().nat;
                Ok(le_witness(d, &nat_prelude, mag_a, mag_b))
            }
            (IntShape::OfNat, IntShape::NegSucc) => Err(Decline::Undecidable),
            (IntShape::NegSucc, IntShape::OfNat) => Ok(d.true_intro()),
            (IntShape::NegSucc, IntShape::NegSucc) => {
                if mag_b > mag_a {
                    return Err(Decline::Undecidable);
                }
                let nat_prelude = d.int().nat;
                Ok(le_witness(d, &nat_prelude, mag_b, mag_a))
            }
        },
        Shape::Lt => match (shape_a, shape_b) {
            (IntShape::OfNat, IntShape::OfNat) => {
                if mag_a >= mag_b {
                    return Err(Decline::Undecidable);
                }
                let nat_prelude = d.int().nat;
                Ok(le_witness(d, &nat_prelude, mag_a + 1, mag_b))
            }
            (IntShape::OfNat, IntShape::NegSucc) => Err(Decline::Undecidable),
            (IntShape::NegSucc, IntShape::OfNat) => Ok(d.true_intro()),
            (IntShape::NegSucc, IntShape::NegSucc) => {
                if mag_b >= mag_a {
                    return Err(Decline::Undecidable);
                }
                let nat_prelude = d.int().nat;
                Ok(le_witness(d, &nat_prelude, mag_b + 1, mag_a))
            }
        },
    }
}

#[cfg(test)]
mod tests;
