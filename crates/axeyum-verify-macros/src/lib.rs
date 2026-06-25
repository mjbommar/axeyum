//! Proc-macro front-end for `axeyum-verify` (scaffold).
//!
//! Phase 1 will parse a `#[axeyum::verify]` function over a restricted Rust
//! surface and emit a bounded symbolic-checking `#[test]`. This file is the
//! de-risking scaffold; the real implementation lands incrementally.
#![forbid(unsafe_code)]

use proc_macro::TokenStream;

/// Placeholder `#[verify]` attribute macro (scaffold): currently a no-op that
/// returns the annotated item unchanged. Phase 1 replaces this body.
#[proc_macro_attribute]
pub fn verify(_attr: TokenStream, item: TokenStream) -> TokenStream {
    item
}
