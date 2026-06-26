//! [`Bounded`] — a range-constrained integer input that emits its own `assume`.
//!
//! Writing `forall::<Bounded<-100, 100>>()` declares a fresh [`Int`] *and*
//! automatically conjoins `-100 <= x <= 100` into the property's hypotheses, so
//! the user never spells the range precondition by hand. The range is carried at
//! the type level (`const LO`/`const HI`), so two different bounds are distinct
//! types and the constraint is fixed at compile time.
//!
//! The wrapped handle is reachable via [`Bounded::value`] (and `Deref`), so a
//! `Bounded` is used in `.check(..)` exactly like the `Int` it wraps:
//!
//! ```rust
//! use axeyum_property::{property, Bounded, Ctx, Int, Outcome};
//!
//! let ctx = Ctx::new();
//! // |x| >= 0 for x in [-1000, 1000] — no manual precondition needed.
//! let outcome = property()
//!     .forall::<Bounded<-1000, 1000>>(&ctx)
//!     .check(|x| x.value().abs().ge(Int::lit(&ctx, 0)))?;
//! assert!(matches!(outcome, Outcome::Proved(_)));
//! # Ok::<(), axeyum_solver::SolverError>(())
//! ```

use std::ops::Deref;

use crate::ctx::Ctx;
use crate::handle::Int;
use crate::property::{Lifted, Slot, Symbolic};

/// A fresh integer input constrained to the inclusive range `[LO, HI]`, with the
/// range `assume` emitted automatically when declared via `forall`.
///
/// `LO` and `HI` are `i128` const generics; `LO <= HI` is the intended use (an
/// empty range makes the precondition unsatisfiable, which the solver handles
/// soundly — every property is then vacuously `Proved`).
#[derive(Clone, Copy)]
pub struct Bounded<'c, const LO: i128, const HI: i128> {
    inner: Int<'c>,
}

impl<'c, const LO: i128, const HI: i128> Bounded<'c, LO, HI> {
    /// The wrapped [`Int`] handle, for use in `.assuming(..)` / `.check(..)`.
    #[must_use]
    pub fn value(self) -> Int<'c> {
        self.inner
    }

    /// The inclusive lower bound (the type-level `LO`).
    #[must_use]
    pub fn lo() -> i128 {
        LO
    }

    /// The inclusive upper bound (the type-level `HI`).
    #[must_use]
    pub fn hi() -> i128 {
        HI
    }
}

impl<'c, const LO: i128, const HI: i128> Deref for Bounded<'c, LO, HI> {
    type Target = Int<'c>;
    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

impl<'c, const LO: i128, const HI: i128> Symbolic<'c> for Bounded<'c, LO, HI> {
    // The counterexample carries the same concrete value an `Int` would.
    type Concrete = i128;

    fn fresh(ctx: &'c Ctx, slots: &mut Vec<Slot>) -> Self {
        // Declare the underlying integer (registers its model slot)...
        let inner = Int::fresh(ctx, slots);
        // ...then emit the range guard `LO <= x <= HI` as an auto-assume the
        // property's `forall` drains into its hypotheses.
        let lo = Int::lit(ctx, LO);
        let hi = Int::lit(ctx, HI);
        ctx.push_auto_assume((lo.le(inner) & inner.le(hi)).term());
        Self { inner }
    }

    fn lift(leaves: &mut impl Iterator<Item = Lifted>) -> Self::Concrete {
        <Int<'c> as Symbolic<'c>>::lift(leaves)
    }
}
