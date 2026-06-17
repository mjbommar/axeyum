//! Hierarchical Lean names (`Name`), interned to lifetime-free [`NameId`]s.
//!
//! A Lean name is a snoc-list of components built on a shared anonymous root:
//! `a.b.1` is `Num(Str(Str(Anon, "a"), "b"), 1)`. The structure is interned in
//! the [`super::Kernel`] arena, so structurally equal names share a single
//! [`NameId`] and equality is an `id == id` comparison.
//!
//! This mirrors nanoda's `name.rs` semantics (`Anon`/`Str`/`Num`) but uses
//! axeyum's `Vec`-backed hash-consing interner instead of a lifetime-tagged
//! arena (ADR-0036).

/// A lifetime-free, `Copy` handle to an interned [`NameNode`].
///
/// IDs are assigned densely in insertion order by the interner, so identical
/// construction sequences yield identical IDs (determinism rule). Using a
/// `NameId` with a different [`super::Kernel`] is a contract violation caught
/// only by bounds checks.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct NameId(pub(crate) u32);

impl NameId {
    /// The index of this name in its owning kernel's name table.
    #[must_use]
    pub fn index(self) -> usize {
        self.0 as usize
    }
}

/// The structural node of a hierarchical name.
///
/// `Anonymous` is the empty root; `Str` and `Num` append a string or numeric
/// component to a parent name. Components are stored by parent [`NameId`], so
/// the node is `Copy`-comparable and hash-consable.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum NameNode {
    /// The empty/anonymous root name.
    Anonymous,
    /// A string component appended to a parent name.
    Str(NameId, String),
    /// A numeric component appended to a parent name.
    Num(NameId, u64),
}
