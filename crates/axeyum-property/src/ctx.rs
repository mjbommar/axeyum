//! The proof context: a [`TermArena`] wrapped for ergonomic shared building.
//!
//! Typed handles ([`crate::Bv`], [`crate::Int`], [`crate::Bool`]) borrow a
//! `&Ctx` so std operator overloading (`a + b`) can build terms without the
//! caller threading a `&mut TermArena` by hand. The arena lives behind a
//! [`RefCell`]; builder calls borrow it mutably for the duration of a single
//! intern and release immediately, so no borrow ever spans a user closure.

use std::cell::{Cell, RefCell};

use axeyum_ir::{SymbolId, TermArena, TermId};

/// Owns the [`TermArena`] every typed handle builds into, plus a monotonic
/// counter for auto-unique symbol names. Construct one with [`Ctx::new`]; hand
/// out `&Ctx`-borrowing handles from it.
///
/// All builder helpers `expect` on the underlying [`axeyum_ir::IrError`]: the
/// typed-handle layer guarantees well-sorted, in-range arguments by
/// construction (type-level bit-vector widths, matched sorts), so an error here
/// is an internal invariant violation, not a user error.
pub struct Ctx {
    arena: RefCell<TermArena>,
    next_id: Cell<u64>,
}

impl Ctx {
    /// Creates a fresh context over an empty arena.
    #[must_use]
    pub fn new() -> Self {
        Self {
            arena: RefCell::new(TermArena::new()),
            next_id: Cell::new(0),
        }
    }

    /// A process-stable, monotonically increasing suffix for auto-named symbols
    /// (`p!0`, `p!1`, …), so repeated `forall` declarations never collide.
    fn fresh_suffix(&self) -> u64 {
        let id = self.next_id.get();
        self.next_id.set(id + 1);
        id
    }

    /// Declares a fresh, uniquely-named bit-vector symbol of `width` bits and
    /// returns its `(SymbolId, TermId)`.
    pub(crate) fn declare_bv(&self, width: u32) -> (SymbolId, TermId) {
        let name = format!("bv{width}!{}", self.fresh_suffix());
        let mut arena = self.arena.borrow_mut();
        let sym = arena
            .declare(&name, axeyum_ir::Sort::BitVec(width))
            .expect("fresh bit-vector declaration is well-formed");
        let term = arena.var(sym);
        (sym, term)
    }

    /// Declares a fresh, uniquely-named integer symbol and returns its
    /// `(SymbolId, TermId)`.
    pub(crate) fn declare_int(&self) -> (SymbolId, TermId) {
        let name = format!("int!{}", self.fresh_suffix());
        let mut arena = self.arena.borrow_mut();
        let sym = arena
            .declare(&name, axeyum_ir::Sort::Int)
            .expect("fresh integer declaration is well-formed");
        let term = arena.var(sym);
        (sym, term)
    }

    /// Declares a fresh, uniquely-named Boolean symbol and returns its
    /// `(SymbolId, TermId)`.
    pub(crate) fn declare_bool(&self) -> (SymbolId, TermId) {
        let name = format!("bool!{}", self.fresh_suffix());
        let mut arena = self.arena.borrow_mut();
        let sym = arena
            .declare(&name, axeyum_ir::Sort::Bool)
            .expect("fresh Boolean declaration is well-formed");
        let term = arena.var(sym);
        (sym, term)
    }

    /// Runs `f` with a mutable borrow of the arena (a single intern), releasing
    /// the borrow before returning. Used by the typed-handle builders.
    pub(crate) fn build<F>(&self, f: F) -> TermId
    where
        F: FnOnce(&mut TermArena) -> TermId,
    {
        let mut arena = self.arena.borrow_mut();
        f(&mut arena)
    }

    /// Like [`Ctx::build`], but the closure returns a `Result`; the
    /// `axeyum_ir::IrError` is unwrapped here (crate-private) so the typed-handle
    /// methods stay panic-free in their public contract.
    ///
    /// The typed-handle layer only ever passes well-sorted, in-range arguments
    /// (type-level widths + matched sorts), so this unwrap is an internal
    /// invariant, never reachable from sound caller code.
    pub(crate) fn build_checked<F>(&self, f: F) -> TermId
    where
        F: FnOnce(&mut TermArena) -> Result<TermId, axeyum_ir::IrError>,
    {
        let mut arena = self.arena.borrow_mut();
        f(&mut arena).expect("typed-handle layer guarantees well-formed term construction")
    }

    /// Gives a closure a mutable borrow of the arena for solving/reconstruction
    /// (which take `&mut TermArena`). The borrow spans the whole call, so it must
    /// not be nested inside another borrow.
    pub(crate) fn with_arena_mut<R>(&self, f: impl FnOnce(&mut TermArena) -> R) -> R {
        let mut arena = self.arena.borrow_mut();
        f(&mut arena)
    }
}

impl Default for Ctx {
    fn default() -> Self {
        Self::new()
    }
}
