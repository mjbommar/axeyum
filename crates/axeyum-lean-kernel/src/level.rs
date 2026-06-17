//! Universe levels (`Level`), interned to lifetime-free [`LevelId`]s.
//!
//! Universe levels form the type-of-types hierarchy: `Zero` is `Prop`'s level,
//! `Succ` steps up, `Max`/`IMax` combine, and `Param` is a universe variable.
//! `IMax l r` is the "impredicative max": it is `Zero` when `r` is `Zero` (so a
//! `Pi` into `Prop` stays in `Prop`), and `Max l r` otherwise.
//!
//! Ported faithfully from nanoda's `level.rs` (`simplify`/`combining`,
//! `subst_level`, and the `leq_core`/`leq_imax_by_cases` antisymmetric
//! comparison), adapted to axeyum's interned [`LevelId`] handles instead of a
//! lifetime-tagged arena (ADR-0036). The `leq`/equiv routines are part of the
//! soundness core of later universe checking, so they are translated
//! line-for-line and exercised by nanoda's level tests.

use crate::name::NameId;

/// A lifetime-free, `Copy` handle to an interned [`LevelNode`].
///
/// IDs are assigned densely in insertion order by the interner (determinism
/// rule). Using a `LevelId` with a different [`super::Kernel`] is a contract
/// violation caught only by bounds checks.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct LevelId(pub(crate) u32);

impl LevelId {
    /// The index of this level in its owning kernel's level table.
    #[must_use]
    pub fn index(self) -> usize {
        self.0 as usize
    }
}

/// The structural node of a universe level.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum LevelNode {
    /// The universe of `Prop` (level `0`).
    Zero,
    /// One above the given level.
    Succ(LevelId),
    /// The larger of two levels.
    Max(LevelId, LevelId),
    /// The impredicative max: `Zero` if the right level is `Zero`, else `Max`.
    IMax(LevelId, LevelId),
    /// A universe parameter (variable) identified by a [`NameId`].
    Param(NameId),
}
