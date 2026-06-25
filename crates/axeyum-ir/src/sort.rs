//! Sorts (types) of terms.

use crate::term::DatatypeId;

/// Handle to an arena-declared uninterpreted sort.
///
/// Like [`DatatypeId`], this is a compact `Copy` id with no lifetime parameter;
/// validity is a contract with the owning [`crate::TermArena`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct SortId(pub(crate) u32);

impl SortId {
    /// The dense index of this declared sort within its arena.
    pub fn index(self) -> usize {
        self.0 as usize
    }
}

/// A sort usable as an array index or element component.
///
/// `Sort` itself stays `Copy`; array components therefore carry this compact
/// non-array sort key rather than boxing recursive `Sort` values. Nested arrays
/// need an interned array-sort id before they become public surface.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ArraySortKey {
    /// The Boolean sort.
    Bool,
    /// Fixed-width bit-vectors.
    BitVec(u32),
    /// The mathematical integer sort.
    Int,
    /// The mathematical real sort.
    Real,
    /// A declared datatype sort.
    Datatype(DatatypeId),
    /// A declared uninterpreted carrier sort.
    Uninterpreted(SortId),
    /// An IEEE 754 floating-point sort.
    Float {
        /// Exponent bits.
        exp: u32,
        /// Significand bits, including the implicit leading bit.
        sig: u32,
    },
}

impl ArraySortKey {
    /// Converts a non-array sort into an array-component key.
    ///
    /// Returns `None` for array sorts; nested arrays are intentionally deferred
    /// until array sort interning is introduced.
    pub fn from_sort(sort: Sort) -> Option<Self> {
        match sort {
            Sort::Bool => Some(ArraySortKey::Bool),
            Sort::BitVec(w) => Some(ArraySortKey::BitVec(w)),
            Sort::Int => Some(ArraySortKey::Int),
            Sort::Real => Some(ArraySortKey::Real),
            Sort::Datatype(id) => Some(ArraySortKey::Datatype(id)),
            Sort::Uninterpreted(id) => Some(ArraySortKey::Uninterpreted(id)),
            Sort::Float { exp, sig } => Some(ArraySortKey::Float { exp, sig }),
            Sort::Array { .. } => None,
        }
    }

    /// Expands this component key back into its ordinary sort.
    pub fn to_sort(self) -> Sort {
        match self {
            ArraySortKey::Bool => Sort::Bool,
            ArraySortKey::BitVec(w) => Sort::BitVec(w),
            ArraySortKey::Int => Sort::Int,
            ArraySortKey::Real => Sort::Real,
            ArraySortKey::Datatype(id) => Sort::Datatype(id),
            ArraySortKey::Uninterpreted(id) => Sort::Uninterpreted(id),
            ArraySortKey::Float { exp, sig } => Sort::Float { exp, sig },
        }
    }

    /// Returns the bit-vector width when this component is a bit-vector sort.
    pub fn bv_width(self) -> Option<u32> {
        match self {
            ArraySortKey::BitVec(w) => Some(w),
            ArraySortKey::Bool
            | ArraySortKey::Int
            | ArraySortKey::Real
            | ArraySortKey::Datatype(_)
            | ArraySortKey::Uninterpreted(_)
            | ArraySortKey::Float { .. } => None,
        }
    }
}

impl core::fmt::Display for ArraySortKey {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            ArraySortKey::Bool => write!(f, "Bool"),
            ArraySortKey::BitVec(w) => write!(f, "(_ BitVec {w})"),
            ArraySortKey::Int => write!(f, "Int"),
            ArraySortKey::Real => write!(f, "Real"),
            ArraySortKey::Datatype(id) => write!(f, "(Datatype {})", id.index()),
            ArraySortKey::Uninterpreted(id) => write!(f, "(Uninterpreted {})", id.index()),
            ArraySortKey::Float { exp, sig } => write!(f, "(_ FloatingPoint {exp} {sig})"),
        }
    }
}

/// Maximum bit-vector width. Values `≤ 128` use the `u128` representation;
/// wider ones (up to this cap) use the limb-based wide representation
/// ([`crate::WideUint`], `Value::WideBv`), which the evaluator and bit-blaster
/// handle. The cap is a generous backstop against runaway memory, not a
/// semantic limit (ADR-0003 set the original `128`; wide-BV lifted it).
pub const MAX_BV_WIDTH: u32 = 1 << 16;

/// The sort (type) of a term.
///
/// `Bool` and `BitVec(1)` are deliberately distinct sorts with no implicit
/// conversion (see the glossary and ADR-0003). `Sort` is a `Copy` enum
/// rather than an interned ID until recursive sorts (arrays) arrive. Declared
/// uninterpreted sorts still live behind an arena-local id so many-sorted EUF
/// does not need to collapse every carrier to a fixed bit-vector width.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Sort {
    /// The Boolean sort.
    Bool,
    /// Fixed-width bit-vectors; width is in bits, `1..=MAX_BV_WIDTH`.
    BitVec(u32),
    /// A total map from the index sort to the element sort (ADR-0010).
    Array {
        /// Index sort.
        index: ArraySortKey,
        /// Element sort.
        element: ArraySortKey,
    },
    /// The mathematical integer sort (linear integer arithmetic, ADR-0014).
    Int,
    /// The mathematical real sort (linear real arithmetic, ADR-0015).
    Real,
    /// A first-class (possibly recursive) datatype sort (ADR-0022); recursion
    /// lives behind the interned id, so `Sort` stays `Copy`.
    Datatype(DatatypeId),
    /// A first-class uninterpreted carrier sort declared by name in the owning
    /// arena. The semantics are pure equality/congruence; concrete models use
    /// deterministic finite class tokens for replay.
    Uninterpreted(SortId),
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
            | Sort::Uninterpreted(_)
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
            Sort::Bool
            | Sort::Array { .. }
            | Sort::Int
            | Sort::Real
            | Sort::Datatype(_)
            | Sort::Uninterpreted(_) => None,
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
            | Sort::Datatype(_)
            | Sort::Uninterpreted(_) => None,
        }
    }

    /// Returns the `(index, element)` widths for an array sort, else `None`.
    ///
    /// This is the compatibility helper for the existing finite-BV array model.
    /// General arrays use [`Sort::array_sorts`].
    pub fn array_widths(self) -> Option<(u32, u32)> {
        match self {
            Sort::Array { index, element } => Some((index.bv_width()?, element.bv_width()?)),
            Sort::Bool
            | Sort::BitVec(_)
            | Sort::Int
            | Sort::Real
            | Sort::Datatype(_)
            | Sort::Uninterpreted(_)
            | Sort::Float { .. } => None,
        }
    }

    /// Returns the `(index, element)` component sorts for an array sort.
    pub fn array_sorts(self) -> Option<(Sort, Sort)> {
        match self {
            Sort::Array { index, element } => Some((index.to_sort(), element.to_sort())),
            Sort::Bool
            | Sort::BitVec(_)
            | Sort::Int
            | Sort::Real
            | Sort::Datatype(_)
            | Sort::Uninterpreted(_)
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
                write!(f, "(Array {index} {element})")
            }
            Sort::Int => write!(f, "Int"),
            Sort::Real => write!(f, "Real"),
            Sort::Datatype(id) => write!(f, "(Datatype {})", id.index()),
            Sort::Uninterpreted(id) => write!(f, "(Uninterpreted {})", id.index()),
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
