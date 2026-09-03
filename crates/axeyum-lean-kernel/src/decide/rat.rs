//! `decide` over ℚ — reusing [`super::int`] rather than re-deriving it.
//!
//! `Rat.le`/`Rat.lt` are `Definition`s over `Int.le`/`Int.lt` by
//! cross-multiplication (`rat_prelude::defs::declare_order`'s own doc:
//! `le q r := Int.le (num q * ofNat (den r)) (num r * ofNat (den q))`), so
//! this producer builds that SAME cross-multiplication term explicitly
//! (`rat_prelude::ops::{num, den_z}` + `IntDev::imul`) and hands it to
//! [`super::int::run`], then relies on the kernel's own `def_eq` to accept
//! the result against the ORIGINAL `Rat.le`/`Rat.lt` goal — the
//! definitional-identity trick every producer in this crate already uses,
//! chained through a second `Definition` layer.
//!
//! **This is deliberately NOT "`whnf` the whole goal and delegate"**, which
//! was the first thing tried: `Int.le`/`Int.lt` are THEMSELVES four-case
//! `Definition`s over `Int.rec` (`super::int`'s own module docs), so a
//! blind `whnf` of `Rat.le lhs rhs` keeps unfolding past the `Int.le`
//! layer into ITS `Int.rec`-based case split — which gets STUCK on the
//! not-yet-evaluated `Int.mul` cross-product argument (not a bare
//! `ofNat`/`negSucc` constructor) and lands on `Int.rec`'s own head, which
//! neither this producer's nor `super::int`'s goal parser recognises.
//! Confirmed by running the naive version first and seeing
//! `super::int::parse_goal` decline `GoalNotAtomic` on a head that was
//! `Int.rec`, not `Int.le`, not by reading the definition ahead of time.
//!
//! `Eq Rat` is NOT a cross-multiplication definition (`Rat`'s equality is
//! ordinary constructor equality of a reduced representative — see
//! `rat_prelude::core`'s own module docs on why cross-multiplication is
//! needed to PROVE two DIFFERENT representations equal, which is a
//! capability this producer does not attempt), so a closed `Eq Rat a b`
//! goal is instead decided by peeling BOTH sides to `(Rat.num, Rat.den)` —
//! `Rat.num` is `Int`-valued ([`super::int::int_value`] peels it directly),
//! `Rat.den` is `Nat`-valued ([`super::nat_value`]) — and comparing. Two
//! reduced `Rat` values with equal `(num, den)` pairs are the SAME term up
//! to the kernel's definitional proof irrelevance on the two proof fields
//! (`Rat.mk`'s positivity/reducedness arguments), so `rat_prelude::ops::rrefl`
//! on one side is a genuine proof of the other; two values that reach this
//! producer with DIFFERENT `(num, den)` pairs are declined, not claimed
//! unequal — a hand-built non-reduced `Rat.mk` application could in
//! principle need cross-multiplication to prove equal to its reduced form,
//! but every `Rat` value any other part of this crate actually constructs
//! is already reduced by construction, so this is not a completeness gap
//! against a real goal population.

use crate::RatPrelude;
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::int_prelude::ops::Shape as IntShape;
use crate::rat_prelude::ops::{den, den_z, num, rat_ty, rrefl};

use super::{Decline, Shape, head_const, is_closed, nat_value, spine};

/// Parse `goal` as `Eq Rat lhs rhs`, `Rat.le lhs rhs`, or `Rat.lt lhs rhs`.
#[cfg_attr(not(test), allow(dead_code))]
fn parse_goal(d: &mut IntDev<'_>, p: &RatPrelude, e: ExprId) -> Option<(Shape, ExprId, ExprId)> {
    let (head, args) = spine(d, e);
    let name = head_const(d, head)?;
    let ty = rat_ty(d);
    if name == p.int.logic.eq && args.len() == 3 && args[0] == ty {
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

/// Peel a closed `Rat` value `q` to `(num shape+magnitude, den magnitude)` —
/// `Rat.num q` (an `Int`, via [`super::int::int_value`]) and `Rat.den q` (a
/// `Nat`, via [`super::nat_value`]).
#[cfg_attr(not(test), allow(dead_code))]
fn rat_value(d: &mut IntDev<'_>, q: ExprId) -> Result<((IntShape, u32), u32), Decline> {
    let n = num(d, q);
    let nv = super::int::int_value(d, n)?;
    let dd = den(d, q);
    let nat_prelude = d.int().nat;
    let dv = nat_value(d, &nat_prelude, dd)?;
    Ok((nv, dv))
}

/// Prove `goal`, a closed `Eq Rat`, `Rat.le`, or `Rat.lt` proposition, by
/// kernel reduction, or decline.
///
/// # Errors
///
/// [`Decline::NotClosed`] on a free variable, [`Decline::GoalNotAtomic`] on
/// an unrecognised shape, [`Decline::Undecidable`] when peeling does not
/// settle within [`super::MAX_MAGNITUDE`] or the two sides genuinely
/// disagree.
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) fn run(d: &mut IntDev<'_>, p: &RatPrelude, goal: ExprId) -> Result<ExprId, Decline> {
    if !is_closed(d, goal) {
        return Err(Decline::NotClosed);
    }
    let (shape, lhs, rhs) = parse_goal(d, p, goal).ok_or(Decline::GoalNotAtomic)?;
    match shape {
        Shape::Eq => {
            let a = rat_value(d, lhs)?;
            let b = rat_value(d, rhs)?;
            if a == b {
                Ok(rrefl(d, lhs))
            } else {
                Err(Decline::Undecidable)
            }
        }
        Shape::Le | Shape::Lt => {
            // `Rat.le`/`Rat.lt` unfold to `Int.le`/`Int.lt` (one delta+beta
            // step) applied to `Int.mul (num lhs) (den_z rhs)` and its
            // mirror -- built explicitly here, NOT recovered by `whnf`ing
            // the whole goal: `Int.le`/`Int.lt` are THEMSELVES four-case
            // `Definition`s (`super::int`'s own module docs), so a blind
            // `whnf` keeps unfolding past them into their `Int.rec`-based
            // case split, which gets STUCK on the not-yet-evaluated
            // `Int.mul` argument and lands on `Int.rec`'s own head, not
            // `Int.le`/`Int.lt` -- confirmed by running this the naive way
            // first and finding `super::int::parse_goal` failed
            // `GoalNotAtomic` on a head that was neither `Int.le` nor
            // `Int.lt`, not by inspecting the definition ahead of time.
            let left = {
                let n = num(d, lhs);
                let dz = den_z(d, rhs);
                d.imul(n, dz)
            };
            let right = {
                let n = num(d, rhs);
                let dz = den_z(d, lhs);
                d.imul(n, dz)
            };
            let int_goal = match shape {
                Shape::Le => d.ile(left, right),
                Shape::Lt => d.ilt(left, right),
                Shape::Eq => unreachable!("handled above"),
            };
            super::int::run(d, int_goal)
        }
    }
}

#[cfg(test)]
mod tests;
