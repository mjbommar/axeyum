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

mod algebraic_bridge;
mod arena;
mod bits;
/// Deterministic work budgets: the stack-wide resource-limit primitive.
///
/// This lives in the IR crate for the same reason [`fast_map`] does — it is a
/// dependency-free utility that every layer above needs, and this is the
/// lowest crate all of them already depend on. It is not about terms; it is
/// about how any pass in any division decides how much work it may do, without
/// reading a clock. Adding a crate for it would need an ADR (ADR-0001 keeps the
/// crate split minimal until a boundary is proven by use).
pub mod budget;
/// Environment levers over compiled caps: an A/B without a rebuild.
///
/// Here for the same reason [`budget`] is: `axeyum-rewrite` and
/// `axeyum-solver` both hold completeness caps that need one lever mechanism,
/// and this is the lowest crate both already depend on. It is not about terms;
/// it is about how a cap that nobody has measured becomes measurable without a
/// workspace rebuild.
pub mod config_lever;
mod error;
mod eval;
pub mod fast_map;
mod fmt;
mod int_wide;
pub mod poly;
pub mod poly_big;
mod rational;
mod real_algebraic;
mod sort;
mod stats;
/// Cooperative stop: "this thread's search is no longer wanted".
///
/// Here for the same reason [`budget`] is: it is the one channel that both
/// `axeyum-solver`'s theory routes and `axeyum-cnf`'s CDCL core have to be
/// able to read, and this is the lowest crate both already depend on.
pub mod stop;
mod term;
mod value;
mod wide;

pub use arena::TermArena;
pub use bits::{
    BIT_VECTOR_WIRE_ORDER, BitOrder, bv_value_to_lsb_bits, lsb_bits_to_bv_value, lsb_bits_to_value,
    value_to_lsb_bits,
};
pub use error::IrError;
pub use eval::{Assignment, DtSelectWitness, eval, eval_with_memo, well_founded_default};
pub use fast_map::{FastMap, FastSet};
pub use fmt::render;
pub use int_wide::WideInt;
pub use rational::Rational;
pub use real_algebraic::{RealAlgebraic, Sign};
pub use sort::{ArraySortKey, MAX_BV_WIDTH, Sort, SortId};
pub use stats::TermStats;
pub use term::{ConstructorId, DatatypeId, FuncId, Op, SymbolId, TermId, TermNode};
pub use value::{ArrayValue, FuncValue, GenericArrayValue, Value};
pub use wide::WideUint;
