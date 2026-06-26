//! [`BvArray`] — a fixed-length symbolic bit-vector array (`[Bv<EW>; N]`).
//!
//! Backed by an SMT array sort `BitVec(32) -> BitVec(EW)` (`Sort::Array`), with a
//! logical length `N` carried at the type level. Indexing comes in two flavours:
//!
//! - [`BvArray::get`] — a *static* read at a compile-known position `i < N`
//!   (the index literal is in bounds by construction, no guard).
//! - [`BvArray::select`] — a *symbolic* read at a [`Bv`] index; declaring the
//!   array via `forall` auto-assumes the in-bounds guard `idx < N`, so the
//!   property is only required to hold for in-range accesses (out-of-bounds is
//!   not silently modelled as some arbitrary value).
//!
//! A counterexample lifts back to a concrete `[u128; N]` (elements `0..N`).

use crate::ctx::Ctx;
use crate::handle::Bv;
use crate::property::{Lifted, Slot, Symbolic};

/// The fixed index width all [`BvArray`]s use (32 bits addresses any practical
/// fixed length).
pub(crate) const INDEX_WIDTH: u32 = 32;

/// A symbolic fixed-length array of `N` bit-vectors of width `EW`.
///
/// `EW` is the element width in bits; `N` is the logical length. Reads are
/// width-checked at the type level (a `get`/`select` yields a `Bv<EW>`).
#[derive(Clone, Copy)]
pub struct BvArray<'c, const EW: u32, const N: usize> {
    ctx: &'c Ctx,
    /// The current array term (`store` threads an updated one through).
    term: axeyum_ir::TermId,
}

impl<'c, const EW: u32, const N: usize> BvArray<'c, EW, N> {
    pub(crate) fn wrap(ctx: &'c Ctx, term: axeyum_ir::TermId) -> Self {
        Self { ctx, term }
    }

    /// The underlying interned array term id.
    #[must_use]
    pub fn term(self) -> axeyum_ir::TermId {
        self.term
    }

    /// The logical length `N`.
    #[must_use]
    pub fn len() -> usize {
        N
    }

    /// Whether the logical length is zero (here only to satisfy clippy's
    /// `len_without_is_empty`; a zero-length array carries no readable element).
    #[must_use]
    pub fn is_empty() -> bool {
        N == 0
    }

    /// A static read at the compile-known position `i` (must be `< N`).
    ///
    /// # Panics
    ///
    /// Panics if `i >= N` — an out-of-range *static* index is a programming
    /// error, caught immediately rather than mis-modelled.
    #[must_use]
    pub fn get(self, i: usize) -> Bv<'c, EW> {
        assert!(i < N, "BvArray::get index {i} out of range 0..{N}");
        let idx = Bv::<INDEX_WIDTH>::lit(self.ctx, i as u128);
        self.select_term(idx.term())
    }

    /// A symbolic read at bit-vector index `idx`. Declaring the array via
    /// `forall` auto-assumes `idx <u N`, so the property only needs to hold for
    /// in-bounds accesses.
    #[must_use]
    pub fn select(self, idx: Bv<'c, INDEX_WIDTH>) -> Bv<'c, EW> {
        // In-bounds guard: idx <u N. Pushed as an auto-assume (a hypothesis).
        let bound = Bv::<INDEX_WIDTH>::lit(self.ctx, N as u128);
        self.ctx.push_auto_assume(idx.ult(bound).term());
        self.select_term(idx.term())
    }

    /// A functional store: returns a new array equal to `self` except position
    /// `idx` holds `val`. Does not mutate `self`.
    #[must_use]
    pub fn store(self, idx: Bv<'c, INDEX_WIDTH>, val: Bv<'c, EW>) -> Self {
        let term = self
            .ctx
            .build_checked(|a| a.store(self.term, idx.term(), val.term()));
        Self::wrap(self.ctx, term)
    }

    fn select_term(self, idx: axeyum_ir::TermId) -> Bv<'c, EW> {
        let term = self.ctx.build_checked(|a| a.select(self.term, idx));
        Bv::wrap(self.ctx, term)
    }
}

impl<'c, const EW: u32, const N: usize> Symbolic<'c> for BvArray<'c, EW, N> {
    type Concrete = [u128; N];

    fn fresh(ctx: &'c Ctx, slots: &mut Vec<Slot>) -> Self {
        let (sym, term) = ctx.declare_array(INDEX_WIDTH, EW);
        slots.push(Slot::array(sym, N));
        Self::wrap(ctx, term)
    }

    fn lift(leaves: &mut impl Iterator<Item = Lifted>) -> Self::Concrete {
        match leaves.next() {
            Some(Lifted::Array(elems)) => {
                let mut out = [0u128; N];
                for (slot, v) in out.iter_mut().zip(elems) {
                    *slot = v;
                }
                out
            }
            other => panic!("BvArray::lift expected an array leaf, got {other:?}"),
        }
    }
}
