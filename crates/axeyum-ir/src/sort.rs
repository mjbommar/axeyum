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

/// Handle to an arena-interned array sort, used as the recursive component of
/// [`ArraySortKey::Array`] (ADR-1955, ADR-1965).
///
/// Like [`DatatypeId`] and [`SortId`] this is a compact `Copy` id with no
/// lifetime parameter, so `Sort` and `ArraySortKey` stay `Copy` and the
/// hash-consing key [`crate::TermNode`] keeps `Hash + Eq`. Validity is a
/// contract with the owning [`crate::TermArena`]: expand it with
/// [`crate::TermArena::array_sort_components`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ArraySortId(pub(crate) u32);

impl ArraySortId {
    /// The dense index of this interned array sort within its arena.
    pub fn index(self) -> usize {
        self.0 as usize
    }
}

/// A sort usable as an array index or element component.
///
/// `Sort` itself stays `Copy`; array components therefore carry this compact
/// sort key rather than boxing recursive `Sort` values. A **nested** array
/// component carries [`ArraySortKey::Array`], an arena-interned id, for the
/// same reason recursive datatypes carry [`DatatypeId`].
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
    /// The five-element SMT-LIB floating-point rounding-mode sort.
    RoundingMode,
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
    /// A **nested** array component: the id of an array sort interned in the
    /// owning arena (ADR-1955 option B). Every arena-free helper on this type
    /// returns `None` for this variant, so a route that cannot handle nesting
    /// refuses by construction rather than by audit; expand it with
    /// [`crate::TermArena::array_sort_components`].
    Array(ArraySortId),
}

impl ArraySortKey {
    /// Converts a non-array sort into an array-component key.
    ///
    /// Returns `None` for array and sequence sorts: an array component cannot
    /// be built without the arena that interns it. Use
    /// [`crate::TermArena::array_sort_key`] to intern a nested component.
    pub fn from_sort(sort: Sort) -> Option<Self> {
        match sort {
            Sort::Bool => Some(ArraySortKey::Bool),
            Sort::BitVec(w) => Some(ArraySortKey::BitVec(w)),
            Sort::Int => Some(ArraySortKey::Int),
            Sort::Real => Some(ArraySortKey::Real),
            Sort::RoundingMode => Some(ArraySortKey::RoundingMode),
            Sort::Datatype(id) => Some(ArraySortKey::Datatype(id)),
            Sort::Uninterpreted(id) => Some(ArraySortKey::Uninterpreted(id)),
            Sort::Float { exp, sig } => Some(ArraySortKey::Float { exp, sig }),
            Sort::Array { .. } | Sort::Seq(_) => None,
        }
    }

    /// Expands this component key back into its ordinary sort **without the
    /// arena**, or `None` when the component is itself an array.
    ///
    /// The `None` is the conservative default that carries the soundness of the
    /// nested-array work: a nested component cannot be expanded without
    /// [`crate::TermArena::array_sort_components`], so every caller that has no
    /// arena to hand must refuse, and refusing is what a route with no nested
    /// support must do anyway. Callers that *can* handle nesting use
    /// [`crate::TermArena::array_key_sort`].
    pub fn to_sort(self) -> Option<Sort> {
        match self {
            ArraySortKey::Bool => Some(Sort::Bool),
            ArraySortKey::BitVec(w) => Some(Sort::BitVec(w)),
            ArraySortKey::Int => Some(Sort::Int),
            ArraySortKey::Real => Some(Sort::Real),
            ArraySortKey::RoundingMode => Some(Sort::RoundingMode),
            ArraySortKey::Datatype(id) => Some(Sort::Datatype(id)),
            ArraySortKey::Uninterpreted(id) => Some(Sort::Uninterpreted(id)),
            ArraySortKey::Float { exp, sig } => Some(Sort::Float { exp, sig }),
            ArraySortKey::Array(_) => None,
        }
    }

    /// The interned id when this component is itself an array sort.
    pub fn nested_array(self) -> Option<ArraySortId> {
        match self {
            ArraySortKey::Array(id) => Some(id),
            ArraySortKey::Bool
            | ArraySortKey::BitVec(_)
            | ArraySortKey::Int
            | ArraySortKey::Real
            | ArraySortKey::RoundingMode
            | ArraySortKey::Datatype(_)
            | ArraySortKey::Uninterpreted(_)
            | ArraySortKey::Float { .. } => None,
        }
    }

    /// Whether this component is itself an array sort.
    pub fn is_nested_array(self) -> bool {
        matches!(self, ArraySortKey::Array(_))
    }

    /// Returns the bit-vector width when this component is a bit-vector sort.
    pub fn bv_width(self) -> Option<u32> {
        match self {
            ArraySortKey::BitVec(w) => Some(w),
            ArraySortKey::Bool
            | ArraySortKey::Int
            | ArraySortKey::Real
            | ArraySortKey::RoundingMode
            | ArraySortKey::Datatype(_)
            | ArraySortKey::Uninterpreted(_)
            | ArraySortKey::Float { .. }
            | ArraySortKey::Array(_) => None,
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
            ArraySortKey::RoundingMode => write!(f, "RoundingMode"),
            ArraySortKey::Datatype(id) => write!(f, "(Datatype {})", id.index()),
            ArraySortKey::Uninterpreted(id) => write!(f, "(Uninterpreted {})", id.index()),
            ArraySortKey::Float { exp, sig } => write!(f, "(_ FloatingPoint {exp} {sig})"),
            // An interned component cannot name its own parts without the
            // arena. This rendering is for diagnostics only; SMT-LIB output
            // goes through the arena-aware writer in `axeyum-smtlib`.
            ArraySortKey::Array(id) => write!(f, "(Array #{})", id.index()),
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
/// conversion (see the glossary and ADR-0003). `Sort` remains a `Copy` enum:
/// arrays and sequences carry compact [`ArraySortKey`] components instead of
/// boxed recursive sorts. **Nested arrays** live behind the interned
/// [`ArraySortId`] in [`ArraySortKey::Array`] (ADR-1955/ADR-1965), the same way
/// recursive datatypes live behind [`DatatypeId`]; nested sequences remain
/// deferred.
/// Declared uninterpreted sorts live behind an arena-local id so many-sorted EUF
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
    /// The five-element SMT-LIB rounding-mode sort.  It lowers to a canonical
    /// three-bit code (`0..=4`); encodings `5..=7` are not carrier values.
    RoundingMode,
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
    /// A homogeneous **sequence** over a scalar element sort (ADR-0051, P2.7).
    /// Like [`Sort::Array`] it carries a `Copy` [`ArraySortKey`] element (so
    /// `Sort` stays `Copy`); nested sequences (`Seq(Seq …)`) are still deferred.
    /// `String` is the distinguished instance
    /// `Seq(BitVec(18))` — `2^18 > 0x2FFFF`, and the unsigned bit-vector order over
    /// `BitVec(18)` is the Unicode code-point total order.
    Seq(ArraySortKey),
}

impl Sort {
    /// The SMT-LIB `String` sort: a sequence of Unicode code points, represented as
    /// `Seq(BitVec(18))` (`2^18 = 262144 > 0x2FFFF`; the unsigned BV order is the
    /// code-point order). See ADR-0051.
    pub const STRING_ELEM_WIDTH: u32 = 18;

    /// Constructs the `String` sort (`Seq(BitVec(18))`).
    #[must_use]
    pub fn string() -> Sort {
        Sort::Seq(ArraySortKey::BitVec(Sort::STRING_ELEM_WIDTH))
    }

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
            | Sort::RoundingMode
            | Sort::Datatype(_)
            | Sort::Uninterpreted(_)
            | Sort::Float { .. }
            | Sort::Seq(_) => None,
        }
    }

    /// Returns the bit width this sort lowers to: the width for `BitVec`, and
    /// `exp + sig` for a floating-point sort (which is bit-blasted as that many
    /// bits). `None` for sorts with no fixed bit-vector lowering.
    pub fn lowered_width(self) -> Option<u32> {
        match self {
            Sort::BitVec(w) => Some(w),
            Sort::Float { exp, sig } => Some(exp + sig),
            Sort::RoundingMode => Some(3),
            Sort::Bool
            | Sort::Array { .. }
            | Sort::Int
            | Sort::Real
            | Sort::Datatype(_)
            | Sort::Uninterpreted(_)
            | Sort::Seq(_) => None,
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
            | Sort::RoundingMode
            | Sort::Datatype(_)
            | Sort::Uninterpreted(_)
            | Sort::Seq(_) => None,
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
            | Sort::RoundingMode
            | Sort::Datatype(_)
            | Sort::Uninterpreted(_)
            | Sort::Float { .. }
            | Sort::Seq(_) => None,
        }
    }

    /// Returns the `(index, element)` component sorts for an array sort, or
    /// `None` for a non-array sort **or for an array with a nested component**.
    ///
    /// The second `None` is load-bearing: it is what keeps every route that
    /// predates nested arrays conservative without an audit of each one. A
    /// route that *can* handle nesting must ask the arena instead
    /// ([`crate::TermArena::array_component_sorts`]).
    pub fn array_sorts(self) -> Option<(Sort, Sort)> {
        match self {
            Sort::Array { index, element } => Some((index.to_sort()?, element.to_sort()?)),
            Sort::Bool
            | Sort::BitVec(_)
            | Sort::Int
            | Sort::Real
            | Sort::RoundingMode
            | Sort::Datatype(_)
            | Sort::Uninterpreted(_)
            | Sort::Float { .. }
            | Sort::Seq(_) => None,
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
            Sort::RoundingMode => write!(f, "RoundingMode"),
            Sort::Datatype(id) => write!(f, "(Datatype {})", id.index()),
            Sort::Uninterpreted(id) => write!(f, "(Uninterpreted {})", id.index()),
            Sort::Float { exp, sig } => write!(f, "(_ FloatingPoint {exp} {sig})"),
            Sort::Seq(element) => write!(f, "(Seq {element})"),
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
