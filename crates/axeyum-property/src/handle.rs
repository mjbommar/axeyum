//! Typed term handles with type-level bit-vector widths.
//!
//! [`Bv<W>`], [`Int`], and [`Bool`] are `Copy` newtypes over an
//! `axeyum_ir::TermId` plus a borrow of the building [`Ctx`]. The width `W` is a
//! const generic, so a `Bv<32> + Bv<64>` is a **compile error** (Z3's
//! `BV::new_const("x", 32)` defers width to a runtime panic). Comparison and
//! arithmetic build directly onto the shared arena via std operator traits and
//! methods; `.equals(..)` returns a [`Bool`] (we deliberately do **not** impl
//! `PartialEq`, which would silently produce a `bool`, not a solver term).
//!
//! Construction is panic-free in its public contract: all builders route through
//! [`Ctx::build_checked`], and the typed-handle layer only ever forms well-sorted,
//! in-range terms (matched sorts, type-level widths), so the underlying
//! `axeyum_ir::IrError` is an unreachable internal invariant.

use std::ops::{Add, BitAnd, BitOr, BitXor, Mul, Neg, Shl, Shr, Sub};

use axeyum_ir::TermId;

use crate::ctx::Ctx;

/// A bit-vector term of statically-known width `W` (in bits).
///
/// Width is enforced by the type system: operators are only defined between two
/// `Bv<W>` of the *same* `W`, so a width mismatch never reaches the solver.
///
/// Mixing widths is a **compile error** (not a runtime panic like z3.rs):
///
/// ```compile_fail
/// use axeyum_property::{Bv, Ctx};
/// let ctx = Ctx::new();
/// let a: Bv<32> = Bv::lit(&ctx, 1);
/// let b: Bv<64> = Bv::lit(&ctx, 1);
/// let _ = a + b; // error[E0308]: mismatched types — `Bv<32>` vs `Bv<64>`
/// ```
#[derive(Clone, Copy)]
pub struct Bv<'c, const W: u32> {
    pub(crate) ctx: &'c Ctx,
    pub(crate) term: TermId,
}

/// A mathematical-integer term (`Sort::Int`), exact within the solver's
/// reference range.
#[derive(Clone, Copy)]
pub struct Int<'c> {
    pub(crate) ctx: &'c Ctx,
    pub(crate) term: TermId,
}

/// A Boolean term (`Sort::Bool`) — the type a property and its precondition
/// evaluate to.
#[derive(Clone, Copy)]
pub struct Bool<'c> {
    pub(crate) ctx: &'c Ctx,
    pub(crate) term: TermId,
}

impl<'c, const W: u32> Bv<'c, W> {
    pub(crate) fn wrap(ctx: &'c Ctx, term: TermId) -> Self {
        Self { ctx, term }
    }

    /// The underlying interned term id.
    #[must_use]
    pub fn term(self) -> TermId {
        self.term
    }

    /// The width in bits (the type-level `W`).
    #[must_use]
    pub fn width() -> u32 {
        W
    }

    /// A width-`W` bit-vector literal. `value` is masked to `W` bits.
    #[must_use]
    pub fn lit(ctx: &'c Ctx, value: u128) -> Self {
        let masked = if W >= 128 {
            value
        } else {
            value & ((1u128 << W) - 1)
        };
        Self::wrap(ctx, ctx.build_checked(|a| a.bv_const(W, masked)))
    }

    /// Unsigned less-than (`bvult`).
    #[must_use]
    pub fn ult(self, rhs: Self) -> Bool<'c> {
        Bool::wrap(
            self.ctx,
            self.ctx.build_checked(|a| a.bv_ult(self.term, rhs.term)),
        )
    }

    /// Unsigned less-than-or-equal (`bvule`).
    #[must_use]
    pub fn ule(self, rhs: Self) -> Bool<'c> {
        Bool::wrap(
            self.ctx,
            self.ctx.build_checked(|a| a.bv_ule(self.term, rhs.term)),
        )
    }

    /// Unsigned greater-than (`bvugt`).
    #[must_use]
    pub fn ugt(self, rhs: Self) -> Bool<'c> {
        Bool::wrap(
            self.ctx,
            self.ctx.build_checked(|a| a.bv_ugt(self.term, rhs.term)),
        )
    }

    /// Unsigned greater-than-or-equal (`bvuge`).
    #[must_use]
    pub fn uge(self, rhs: Self) -> Bool<'c> {
        Bool::wrap(
            self.ctx,
            self.ctx.build_checked(|a| a.bv_uge(self.term, rhs.term)),
        )
    }

    /// Signed less-than (`bvslt`).
    #[must_use]
    pub fn slt(self, rhs: Self) -> Bool<'c> {
        Bool::wrap(
            self.ctx,
            self.ctx.build_checked(|a| a.bv_slt(self.term, rhs.term)),
        )
    }

    /// Signed less-than-or-equal (`bvsle`).
    #[must_use]
    pub fn sle(self, rhs: Self) -> Bool<'c> {
        Bool::wrap(
            self.ctx,
            self.ctx.build_checked(|a| a.bv_sle(self.term, rhs.term)),
        )
    }

    /// Signed greater-than (`bvsgt`).
    #[must_use]
    pub fn sgt(self, rhs: Self) -> Bool<'c> {
        Bool::wrap(
            self.ctx,
            self.ctx.build_checked(|a| a.bv_sgt(self.term, rhs.term)),
        )
    }

    /// Signed greater-than-or-equal (`bvsge`).
    #[must_use]
    pub fn sge(self, rhs: Self) -> Bool<'c> {
        Bool::wrap(
            self.ctx,
            self.ctx.build_checked(|a| a.bv_sge(self.term, rhs.term)),
        )
    }

    /// Bit-vector equality, as a [`Bool`] term (not `PartialEq`).
    #[must_use]
    pub fn equals(self, rhs: Self) -> Bool<'c> {
        Bool::wrap(
            self.ctx,
            self.ctx.build_checked(|a| a.eq(self.term, rhs.term)),
        )
    }

    /// Wrapping (modular `2^W`) addition — the explicit name for the `+` operator.
    #[must_use]
    pub fn wrapping_add(self, rhs: Self) -> Self {
        self + rhs
    }

    /// Wrapping (modular `2^W`) subtraction.
    #[must_use]
    pub fn wrapping_sub(self, rhs: Self) -> Self {
        self - rhs
    }

    /// Wrapping (modular `2^W`) multiplication.
    #[must_use]
    pub fn wrapping_mul(self, rhs: Self) -> Self {
        self * rhs
    }

    /// Unsigned-add-overflow predicate (`bvuaddo`): true iff `self + rhs`
    /// overflows the `W`-bit unsigned range.
    #[must_use]
    pub fn add_overflows(self, rhs: Self) -> Bool<'c> {
        Bool::wrap(
            self.ctx,
            self.ctx.build_checked(|a| a.bv_uaddo(self.term, rhs.term)),
        )
    }

    /// Unsigned-subtract-overflow (borrow) predicate (`bvusubo`).
    #[must_use]
    pub fn sub_overflows(self, rhs: Self) -> Bool<'c> {
        Bool::wrap(
            self.ctx,
            self.ctx.build_checked(|a| a.bv_usubo(self.term, rhs.term)),
        )
    }

    /// Unsigned-multiply-overflow predicate (`bvumulo`).
    #[must_use]
    pub fn mul_overflows(self, rhs: Self) -> Bool<'c> {
        Bool::wrap(
            self.ctx,
            self.ctx.build_checked(|a| a.bv_umulo(self.term, rhs.term)),
        )
    }
}

macro_rules! bv_binop {
    ($trait:ident, $method:ident, $build:ident) => {
        impl<'c, const W: u32> $trait for Bv<'c, W> {
            type Output = Bv<'c, W>;
            fn $method(self, rhs: Self) -> Self::Output {
                Bv::wrap(
                    self.ctx,
                    self.ctx.build_checked(|a| a.$build(self.term, rhs.term)),
                )
            }
        }
    };
}

bv_binop!(Add, add, bv_add);
bv_binop!(Sub, sub, bv_sub);
bv_binop!(Mul, mul, bv_mul);
bv_binop!(BitAnd, bitand, bv_and);
bv_binop!(BitOr, bitor, bv_or);
bv_binop!(BitXor, bitxor, bv_xor);
bv_binop!(Shl, shl, bv_shl);
bv_binop!(Shr, shr, bv_lshr);

impl<'c, const W: u32> Neg for Bv<'c, W> {
    type Output = Bv<'c, W>;
    fn neg(self) -> Self::Output {
        Bv::wrap(self.ctx, self.ctx.build_checked(|a| a.bv_neg(self.term)))
    }
}

impl<'c, const W: u32> std::ops::Not for Bv<'c, W> {
    type Output = Bv<'c, W>;
    fn not(self) -> Self::Output {
        Bv::wrap(self.ctx, self.ctx.build_checked(|a| a.bv_not(self.term)))
    }
}

impl<'c> Int<'c> {
    pub(crate) fn wrap(ctx: &'c Ctx, term: TermId) -> Self {
        Self { ctx, term }
    }

    /// The underlying interned term id.
    #[must_use]
    pub fn term(self) -> TermId {
        self.term
    }

    /// An integer literal.
    #[must_use]
    pub fn lit(ctx: &'c Ctx, value: i128) -> Self {
        Self::wrap(ctx, ctx.build(|a| a.int_const(value)))
    }

    /// Integer less-than.
    #[must_use]
    pub fn lt(self, rhs: Self) -> Bool<'c> {
        Bool::wrap(
            self.ctx,
            self.ctx.build_checked(|a| a.int_lt(self.term, rhs.term)),
        )
    }

    /// Integer less-than-or-equal.
    #[must_use]
    pub fn le(self, rhs: Self) -> Bool<'c> {
        Bool::wrap(
            self.ctx,
            self.ctx.build_checked(|a| a.int_le(self.term, rhs.term)),
        )
    }

    /// Integer greater-than.
    #[must_use]
    pub fn gt(self, rhs: Self) -> Bool<'c> {
        Bool::wrap(
            self.ctx,
            self.ctx.build_checked(|a| a.int_gt(self.term, rhs.term)),
        )
    }

    /// Integer greater-than-or-equal.
    #[must_use]
    pub fn ge(self, rhs: Self) -> Bool<'c> {
        Bool::wrap(
            self.ctx,
            self.ctx.build_checked(|a| a.int_ge(self.term, rhs.term)),
        )
    }

    /// Integer equality, as a [`Bool`] term.
    #[must_use]
    pub fn equals(self, rhs: Self) -> Bool<'c> {
        Bool::wrap(
            self.ctx,
            self.ctx.build_checked(|a| a.eq(self.term, rhs.term)),
        )
    }

    /// `|self|` as an `ite(self < 0, -self, self)`.
    #[must_use]
    pub fn abs(self) -> Self {
        let term = self.ctx.build_checked(|a| {
            let zero = a.int_const(0);
            let neg = a.int_neg(self.term)?;
            let is_neg = a.int_lt(self.term, zero)?;
            a.ite(is_neg, neg, self.term)
        });
        Int::wrap(self.ctx, term)
    }
}

impl<'c> Add for Int<'c> {
    type Output = Int<'c>;
    fn add(self, rhs: Self) -> Self::Output {
        Int::wrap(
            self.ctx,
            self.ctx.build_checked(|a| a.int_add(self.term, rhs.term)),
        )
    }
}

impl<'c> Sub for Int<'c> {
    type Output = Int<'c>;
    fn sub(self, rhs: Self) -> Self::Output {
        Int::wrap(
            self.ctx,
            self.ctx.build_checked(|a| a.int_sub(self.term, rhs.term)),
        )
    }
}

impl<'c> Mul for Int<'c> {
    type Output = Int<'c>;
    fn mul(self, rhs: Self) -> Self::Output {
        Int::wrap(
            self.ctx,
            self.ctx.build_checked(|a| a.int_mul(self.term, rhs.term)),
        )
    }
}

impl<'c> Neg for Int<'c> {
    type Output = Int<'c>;
    fn neg(self) -> Self::Output {
        Int::wrap(self.ctx, self.ctx.build_checked(|a| a.int_neg(self.term)))
    }
}

impl<'c> Bool<'c> {
    pub(crate) fn wrap(ctx: &'c Ctx, term: TermId) -> Self {
        Self { ctx, term }
    }

    /// The underlying interned term id.
    #[must_use]
    pub fn term(self) -> TermId {
        self.term
    }

    /// A Boolean literal.
    #[must_use]
    pub fn lit(ctx: &'c Ctx, value: bool) -> Self {
        Self::wrap(ctx, ctx.build(|a| a.bool_const(value)))
    }

    /// Logical negation (the inherent form; `!self` via [`std::ops::Not`] is
    /// equivalent).
    #[must_use]
    pub fn negate(self) -> Self {
        Bool::wrap(self.ctx, self.ctx.build_checked(|a| a.not(self.term)))
    }

    /// Logical implication `self => rhs`.
    #[must_use]
    pub fn implies(self, rhs: Self) -> Self {
        self.negate() | rhs
    }

    /// Boolean equality (iff), as a [`Bool`] term.
    #[must_use]
    pub fn equals(self, rhs: Self) -> Self {
        Bool::wrap(
            self.ctx,
            self.ctx.build_checked(|a| a.eq(self.term, rhs.term)),
        )
    }
}

impl<'c> BitAnd for Bool<'c> {
    type Output = Bool<'c>;
    fn bitand(self, rhs: Self) -> Self::Output {
        Bool::wrap(
            self.ctx,
            self.ctx.build_checked(|a| a.and(self.term, rhs.term)),
        )
    }
}

impl<'c> BitOr for Bool<'c> {
    type Output = Bool<'c>;
    fn bitor(self, rhs: Self) -> Self::Output {
        Bool::wrap(
            self.ctx,
            self.ctx.build_checked(|a| a.or(self.term, rhs.term)),
        )
    }
}

impl<'c> std::ops::Not for Bool<'c> {
    type Output = Bool<'c>;
    fn not(self) -> Self::Output {
        self.negate()
    }
}
