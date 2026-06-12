//! Error types for term construction and evaluation.

use crate::sort::Sort;
use crate::term::SymbolId;

/// Errors produced by term builders and the ground evaluator.
///
/// Build errors are always reported at construction time; per the
/// bv-semantics note, no invalid construction ever becomes a runtime value.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum IrError {
    /// An operand had a different sort than the operator requires.
    SortMismatch {
        /// What the operator required at this position.
        expected: &'static str,
        /// The sort actually found.
        found: Sort,
    },
    /// Two operands were required to have the same sort but differ.
    SortsDiffer(Sort, Sort),
    /// A bit-vector width outside `1..=MAX_BV_WIDTH` (ADR-0003).
    InvalidWidth(u32),
    /// A constant value does not fit in the stated width.
    ValueOutOfRange {
        /// The stated width in bits.
        width: u32,
        /// The offending value.
        value: u128,
    },
    /// `extract` bounds violate `hi >= lo` and `hi < width`.
    ExtractOutOfRange {
        /// High bit index (inclusive).
        hi: u32,
        /// Low bit index (inclusive).
        lo: u32,
        /// Width of the operand.
        width: u32,
    },
    /// A `concat` result would exceed `MAX_BV_WIDTH` (ADR-0003).
    ConcatTooWide(u32),
    /// A bit slice length does not match the requested sort or conversion.
    BitCountMismatch {
        /// Expected number of bits.
        expected: u32,
        /// Actual number of bits.
        found: usize,
    },
    /// A symbol name was redeclared with a different sort.
    SymbolSortConflict {
        /// The conflicting symbol name.
        name: String,
        /// The sort from the original declaration.
        existing: Sort,
        /// The sort from the conflicting declaration.
        requested: Sort,
    },
    /// Evaluation found no value bound for a symbol.
    UnboundSymbol(SymbolId),
}

impl core::fmt::Display for IrError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            IrError::SortMismatch { expected, found } => {
                write!(f, "sort mismatch: expected {expected}, found {found}")
            }
            IrError::SortsDiffer(a, b) => {
                write!(f, "operands must share a sort: {a} vs {b}")
            }
            IrError::InvalidWidth(w) => write!(f, "invalid bit-vector width {w}"),
            IrError::ValueOutOfRange { width, value } => {
                write!(f, "value {value} does not fit in {width} bits")
            }
            IrError::ExtractOutOfRange { hi, lo, width } => {
                write!(f, "extract [{hi}:{lo}] out of range for width {width}")
            }
            IrError::ConcatTooWide(w) => write!(f, "concat result width {w} exceeds maximum"),
            IrError::BitCountMismatch { expected, found } => {
                write!(f, "expected {expected} bits, found {found}")
            }
            IrError::SymbolSortConflict {
                name,
                existing,
                requested,
            } => write!(
                f,
                "symbol `{name}` already declared with sort {existing}, requested {requested}"
            ),
            IrError::UnboundSymbol(s) => write!(f, "no value bound for symbol #{}", s.index()),
        }
    }
}

impl core::error::Error for IrError {}
