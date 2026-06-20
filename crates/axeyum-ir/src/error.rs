//! Error types for term construction and evaluation.

use crate::sort::Sort;
use crate::term::{FuncId, SymbolId};

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
    /// A function name was redeclared with a different signature.
    FunctionSignatureConflict {
        /// The conflicting function name.
        name: String,
    },
    /// An application supplied the wrong number of arguments for a function.
    ArityMismatch {
        /// The declared arity.
        expected: usize,
        /// The number of arguments supplied.
        found: usize,
    },
    /// Evaluation found no interpretation bound for an uninterpreted function.
    UnboundFunction(FuncId),
    /// A quantifier ranges over a domain the evaluator cannot enumerate (an
    /// infinite sort, or a bit-vector wider than the enumeration limit).
    UnsupportedQuantifierDomain(Sort),
    /// A datatype selector was applied to a value built by a different
    /// constructor (ADR-0022); the selection is undefined.
    DatatypeConstructorMismatch,
    /// An arithmetic evaluation result fell outside the `i128` reference range
    /// (e.g. `IntMul` overflow, `abs(i128::MIN)`, a rational whose normalized
    /// numerator/denominator overflows, or `bv2nat` of a value `> i128::MAX`).
    ///
    /// The evaluator is the soundness trust anchor (sat models are accepted only
    /// after replaying against it), so it must never panic or return a wrapped
    /// (wrong) value: an out-of-range result is reported as this error and a
    /// dependent sat model is conservatively *not* accepted (graceful unknown).
    ArithmeticOverflow {
        /// The operator whose evaluation overflowed (a short static label).
        op: &'static str,
    },
    /// A construction is well-typed but not supported by the current encoding
    /// (e.g. a regex Boolean operator nested where only an automaton-expressible
    /// sub-expression is allowed). The string explains the limitation.
    Unsupported(&'static str),
    /// A real-arithmetic operator (`Real{Add,Sub,Mul,Neg,Div}`) was applied to a
    /// [`crate::Value::RealAlgebraic`] operand. Algebraic *field arithmetic* is
    /// deferred past ADR-0038 slice 1, so the evaluator declines exactly (a
    /// graceful error surfaced as `unknown` by callers) rather than returning a
    /// wrong value. The static label names the operator.
    AlgebraicArithmeticUnsupported {
        /// The operator that could not be evaluated (a short static label).
        op: &'static str,
    },
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
            IrError::FunctionSignatureConflict { name } => {
                write!(
                    f,
                    "function `{name}` already declared with a different signature"
                )
            }
            IrError::ArityMismatch { expected, found } => {
                write!(f, "function expects {expected} arguments, found {found}")
            }
            IrError::UnboundFunction(func) => {
                write!(f, "no interpretation bound for function #{}", func.index())
            }
            IrError::UnsupportedQuantifierDomain(sort) => {
                write!(f, "cannot enumerate quantifier domain {sort}")
            }
            IrError::DatatypeConstructorMismatch => {
                write!(f, "datatype selector applied to a different constructor")
            }
            IrError::ArithmeticOverflow { op } => {
                write!(
                    f,
                    "arithmetic overflow evaluating `{op}` (outside i128 range)"
                )
            }
            IrError::Unsupported(why) => write!(f, "unsupported construction: {why}"),
            IrError::AlgebraicArithmeticUnsupported { op } => {
                write!(
                    f,
                    "real-algebraic field arithmetic for `{op}` is not supported (ADR-0038 slice 1)"
                )
            }
        }
    }
}

impl core::error::Error for IrError {}
