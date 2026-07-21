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
//! ## Scalar source contracts
//!
//! A straight-line scalar function may retain its tail result and constrain the
//! checked population with typed `requires` / `ensures` annotations. `verify`
//! must remain the outer attribute so it can consume both inert markers:
//!
//! ```no_run
//! #[axeyum_verify::verify]
//! #[axeyum_verify::requires(x < 255)]
//! #[axeyum_verify::ensures(|result| result == x + 1)]
//! fn checked_inc(x: u8) -> u8 {
//!     x + 1
//! }
//! ```
//!
//! A postcondition counterexample is replayed through a normal call and the
//! original typed closure; it is never reported as a panic. Misordered markers
//! are rejected instead of being silently ignored:
//!
//! ```compile_fail
//! #[axeyum_verify::requires(x < 255)]
//! #[axeyum_verify::verify]
//! #[axeyum_verify::ensures(|result| result == x + 1)]
//! fn misplaced_requires(x: u8) -> u8 {
//!     x + 1
//! }
//! ```
//!
//! ## Soundness floor
//!
//! Every reported counterexample is validated by **actually running the
//! original Rust function** on the witness inputs (the macro-generated test, or
//! [`reproduce`] helpers). A panic-class witness must panic; a postcondition
//! witness must return normally and make the source `ensures` closure false. A
//! witness that does not reproduce its class is a lowering defect, not a
//! finding. BV division is SMT-LIB-total (`÷0` = all-ones), *not* Rust's panic,
//! so `/` and `%` emit an explicit `divisor == 0` bad state.
//!
//! ## Out-of-fragment constructs are rejected at compile time
//!
//! A parameter type (or body construct) outside the whitelisted subset — here a
//! float — is a **clean compile error** from the macro, never a silent
//! mis-model:
//!
//! ```compile_fail
//! #[axeyum_verify::verify]
//! fn uses_a_float(x: f64) -> f64 {
//!     x + 1.0
//! }
//! ```
//!
//! An **unsized slice** `&[T]` (no fixed length) is likewise rejected — the
//! bounded check needs a compile-time element count, so a fixed `&[T; N]` (or
//! `[T; N]`) is required:
//!
//! ```compile_fail
//! #[axeyum_verify::verify]
//! fn reads_a_slice(a: &[u8], i: usize) -> u8 {
//!     a[i]
//! }
//! ```
#![forbid(unsafe_code)]

pub mod ast;
pub mod bmc;
pub mod loop_system;
pub mod lower;
pub mod reflect;
pub mod reproduce;
pub mod verify;

/// Re-export of the `#[verify]` attribute macro.
pub use axeyum_verify_macros::{ensures, requires, verify};

/// Re-export of the `#[unwind(K)]` attribute macro: place it on a `#[verify]`
/// function to set the loop-unwind bound `K` for the bounded check.
pub use axeyum_verify_macros::unwind;

pub use ast::{ArrayParam, BinOp, ContractProgram, Expr, Param, Program, Stmt, Ty, UnOp};
pub use verify::{
    CertCoverage, Verdict, Witness, cert_coverage, default_config, signed_value,
    verify_contract_program, verify_program,
};

/// The modeled `Option` constructor recognized by `#[axeyum::verify]`:
/// `opt(is_some, value).unwrap()` is `Some(value)` when `is_some`, else `None`.
///
/// The verifier treats `is_some` as a symbolic discriminant and flags the
/// `None`-then-`unwrap` path as a panic class. At *runtime* (in the original
/// function and the reproduction) it behaves exactly as the obvious `Option`,
/// so the soundness-floor re-execution is faithful.
#[must_use]
pub fn opt<T>(is_some: bool, value: T) -> Option<T> {
    if is_some { Some(value) } else { None }
}
