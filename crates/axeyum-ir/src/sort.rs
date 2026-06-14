//! Sorts (types) of terms.

use crate::term::DatatypeId;

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
    /// A total map from `BitVec(index)` to `BitVec(element)` (ADR-0010).
    Array {
        /// Index bit-vector width.
        index: u32,
        /// Element bit-vector width.
        element: u32,
    },
    /// The mathematical integer sort (linear integer arithmetic, ADR-0014).
    Int,
    /// The mathematical real sort (linear real arithmetic, ADR-0015).
    Real,
    /// A first-class (possibly recursive) datatype sort (ADR-0022); recursion
    /// lives behind the interned id, so `Sort` stays `Copy`.
    Datatype(DatatypeId),
    /// An IEEE 754 floating-point sort of format `(exp, sig)` bits (ADR-0026).
    /// `exp` is the exponent width and `sig` the total significand width
    /// (including the hidden bit); the value is a `Bv` of width `exp + sig`, so
    /// FP lowers structurally to `BitVec(exp + sig)`. The format lives inline
    /// because `FloatFormat` (in `axeyum-fp`) cannot be referenced from the IR
    /// without a dependency cycle.
    Float {
        /// Exponent bits.
        exp: u32,
        /// Significand bits, including the implicit leading bit.
        sig: u32,
    },
}

impl Sort {
    /// Returns the bit-vector width, or `None` for non-bit-vector sorts.
    ///
    /// A floating-point sort is **not** a bit-vector and returns `None` here even
    /// though it is *represented* as one; use [`Sort::lowered_width`] for the
    /// width shared by both.
    pub fn bv_width(self) -> Option<u32> {
        match self {
            Sort::BitVec(w) => Some(w),
            Sort::Bool
            | Sort::Array { .. }
            | Sort::Int
            | Sort::Real
            | Sort::Datatype(_)
            | Sort::Float { .. } => None,
        }
    }

    /// Returns the bit width this sort lowers to: the width for `BitVec`, and
    /// `exp + sig` for a floating-point sort (which is bit-blasted as that many
    /// bits). `None` for sorts with no fixed bit-vector lowering.
    pub fn lowered_width(self) -> Option<u32> {
        match self {
            Sort::BitVec(w) => Some(w),
            Sort::Float { exp, sig } => Some(exp + sig),
            Sort::Bool | Sort::Array { .. } | Sort::Int | Sort::Real | Sort::Datatype(_) => None,
        }
    }

    /// Returns `true` if this is the Boolean sort.
    pub fn is_bool(self) -> bool {
        self == Sort::Bool
    }

    /// Returns the `(exp, sig)` format of a floating-point sort, else `None`.
    pub fn float_format(self) -> Option<(u32, u32)> {
        match self {
            Sort::Float { exp, sig } => Some((exp, sig)),
            Sort::Bool
            | Sort::BitVec(_)
            | Sort::Array { .. }
            | Sort::Int
            | Sort::Real
            | Sort::Datatype(_) => None,
        }
    }

    /// Returns the `(index, element)` widths for an array sort, else `None`.
    pub fn array_widths(self) -> Option<(u32, u32)> {
        match self {
            Sort::Array { index, element } => Some((index, element)),
            Sort::Bool
            | Sort::BitVec(_)
            | Sort::Int
            | Sort::Real
            | Sort::Datatype(_)
            | Sort::Float { .. } => None,
        }
    }
}

impl core::fmt::Display for Sort {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Sort::Bool => write!(f, "Bool"),
            Sort::BitVec(w) => write!(f, "(_ BitVec {w})"),
            Sort::Array { index, element } => {
                write!(f, "(Array (_ BitVec {index}) (_ BitVec {element}))")
            }
            Sort::Int => write!(f, "Int"),
            Sort::Real => write!(f, "Real"),
            Sort::Datatype(id) => write!(f, "(Datatype {})", id.index()),
            Sort::Float { exp, sig } => write!(f, "(_ FloatingPoint {exp} {sig})"),
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
