//! # axeyum-verify — a bounded Rust verifier (scaffold)
//!
//! A `#[axeyum::verify]` proc-macro that symbolically bounded-checks a Rust
//! function for panics / integer overflow / `unwrap` failures / assertion
//! violations, emitting either a runnable failing `#[test]` (a concrete
//! reproducing input) or a bounded-verified certificate. Built on the
//! `axeyum-property` SDK + `axeyum-solver`.
//!
//! This file is the de-risking scaffold; Phase 1 lands the runtime + lowering.
#![forbid(unsafe_code)]

/// Re-export of the `#[verify]` attribute macro.
pub use axeyum_verify_macros::verify;
