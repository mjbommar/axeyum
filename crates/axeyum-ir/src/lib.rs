//! Typed term IR for the Axeyum automated reasoning stack.
//!
//! This crate owns the core representations: sorts, symbols, terms stored as
//! an interned DAG in an arena with compact `Copy` IDs, typed sort-checked
//! builders, and the ground evaluator that serves as the executable semantic
//! reference for every other layer.
//!
//! Design notes live in the repository under `docs/research/`; the operative
//! decisions are ADR-0001 (vertical slice scope), ADR-0003 (representation
//! choices), and the bv-semantics note (SMT-LIB edge-case semantics).
//!
//! # Example
//!
//! Build `x + 1 == 5` over `BV(8)` and confirm `x = 4` satisfies it:
//!
//! ```
//! use axeyum_ir::{Assignment, Sort, TermArena, Value, eval};
//!
//! let mut arena = TermArena::new();
//! let x_sym = arena.declare("x", Sort::BitVec(8))?;
//! let x = arena.var(x_sym);
//! let one = arena.bv_const(8, 1)?;
//! let five = arena.bv_const(8, 5)?;
//! let sum = arena.bv_add(x, one)?;
//! let formula = arena.eq(sum, five)?;
//!
//! let mut assignment = Assignment::new();
//! assignment.set(x_sym, Value::Bv { width: 8, value: 4 });
//! assert_eq!(eval(&arena, formula, &assignment)?, Value::Bool(true));
//! # Ok::<(), axeyum_ir::IrError>(())
//! ```

mod arena;
mod bits;
mod error;
mod eval;
mod fmt;
pub mod poly;
pub mod poly_big;
mod rational;
mod real_algebraic;
mod sort;
mod stats;
mod term;
mod value;
mod wide;

pub use arena::TermArena;
pub use bits::{
    BIT_VECTOR_WIRE_ORDER, BitOrder, bv_value_to_lsb_bits, lsb_bits_to_bv_value, lsb_bits_to_value,
    value_to_lsb_bits,
};
pub use error::IrError;
pub use eval::{Assignment, eval, eval_with_memo, well_founded_default};
pub use fmt::render;
pub use rational::Rational;
pub use real_algebraic::{RealAlgebraic, Sign};
pub use sort::{ArraySortKey, MAX_BV_WIDTH, Sort, SortId};
pub use stats::TermStats;
pub use term::{ConstructorId, DatatypeId, FuncId, Op, SymbolId, TermId, TermNode};
pub use value::{ArrayValue, FuncValue, GenericArrayValue, Value};
pub use wide::WideUint;
