//! # axeyum-verify — a bounded Rust verifier
//!
//! A `#[axeyum::verify]` proc-macro that symbolically bounded-checks a Rust
//! function for panics / integer overflow / `unwrap` failures / assertion
//! violations, emitting either a runnable failing `#[test]` (a concrete
//! reproducing input) or a bounded-verified certificate. Built on the
//! [`axeyum_property`] SDK + [`axeyum_solver`].
//!
//! ## Pipeline
//!
//! The proc-macro parses the annotated function over a **whitelisted Rust
//! subset** (integers / bools, arithmetic / bitwise / comparison, `let`,
//! `if`/`else`, `assert!`/`panic!`, `unwrap()`-on-`Option`, and
//! `#[axeyum::unwind(K)]`-bounded `for`/`while`) into the runtime [`ast::Program`],
//! then [`verify::verify_program`] lowers it ([`lower`]) into `axeyum-ir` terms
//! with each panic class turned into an explicit *bad state* and decides
//! reachability with the solver:
//!
//! - [`verify::Verdict::Verified`] — no bad state reachable within the unwind
//!   bound (carries whether the safety certificate re-checked);
//! - [`verify::Verdict::Counterexample`] — a concrete bug witness, lifted to
//!   typed [`verify::Witness`] inputs (the macro also emits a runnable failing
//!   `#[test]`);
//! - [`verify::Verdict::Unknown`] — undecided or out-of-fragment, never a wrong
//!   verdict.
//!
//! ## Soundness floor
//!
//! Every reported counterexample is validated by **actually running the
//! original Rust function** on the witness inputs (the macro-generated test, or
//! [`reproduce`] helpers). A witness that does not reproduce a panic is a
//! lowering defect, not a finding. BV division is SMT-LIB-total (`÷0` =
//! all-ones), *not* Rust's panic, so `/` and `%` emit an explicit `divisor == 0`
//! bad state.
#![forbid(unsafe_code)]

pub mod ast;
pub mod lower;
pub mod reproduce;
pub mod verify;

/// Re-export of the `#[verify]` attribute macro.
pub use axeyum_verify_macros::verify;

pub use ast::{ArrayParam, BinOp, Expr, Param, Program, Stmt, Ty, UnOp};
pub use verify::{Verdict, Witness, default_config, signed_value, verify_program};
