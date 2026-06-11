//! Sorts (types) of terms.

/// Maximum bit-vector width supported in M0 (ADR-0003).
pub const MAX_BV_WIDTH: u32 = 128;

/// The sort (type) of a term.
///
/// `Bool` and `BitVec(1)` are deliberately distinct sorts with no implicit
/// conversion (see the glossary and ADR-0003). `Sort` is a `Copy` enum
/// rather than an interned ID until recursive sorts (arrays) arrive.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Sort {
    /// The Boolean sort.
    Bool,
    /// Fixed-width bit-vectors; width is in bits, `1..=MAX_BV_WIDTH`.
    BitVec(u32),
}

impl Sort {
    /// Returns the bit-vector width, or `None` for non-bit-vector sorts.
    pub fn bv_width(self) -> Option<u32> {
        match self {
            Sort::Bool => None,
            Sort::BitVec(w) => Some(w),
        }
    }

    /// Returns `true` if this is the Boolean sort.
    pub fn is_bool(self) -> bool {
        self == Sort::Bool
    }
}

impl core::fmt::Display for Sort {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Sort::Bool => write!(f, "Bool"),
            Sort::BitVec(w) => write!(f, "(_ BitVec {w})"),
        }
    }
}

/// Returns the bit mask covering `width` low bits.
///
/// `width` must already be validated to lie in `1..=MAX_BV_WIDTH`.
pub(crate) fn mask(width: u32) -> u128 {
    if width >= 128 {
        u128::MAX
    } else {
        (1u128 << width) - 1
    }
}
