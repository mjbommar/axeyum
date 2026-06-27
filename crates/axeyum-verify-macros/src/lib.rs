//! Proc-macro front-end for `axeyum-verify`.
//!
//! `#[axeyum::verify]` on a function over a **whitelisted Rust subset**
//! (integers / bools, arithmetic / bitwise / comparison, `let`, `if`/`else`,
//! `assert!`/`assert_eq!`, `panic!`/`unreachable!`, `unwrap()`/`expect()` on
//! `Option`, and `#[axeyum::unwind(K)]`-bounded `for i in 0..K` / `while`) keeps
//! the original function and additionally emits a `#[test]` that lowers the body
//! to the `axeyum-verify` runtime AST and bounded-checks it for panic classes.
//!
//! Anything outside the subset (heap, traits, closures, floats, recursion, ...)
//! is a **clean compile error** at macro time — never silently mis-modeled.
//!
//! On a counterexample the generated test, by construction, also runs the
//! original function on the witness inputs and asserts it panics (the
//! soundness floor / DISAGREE=0 reproduction).
#![forbid(unsafe_code)]

mod parse;

use proc_macro::TokenStream;
use quote::quote;
use syn::{ItemFn, parse_macro_input};

/// The `#[axeyum::verify]` attribute macro. See the crate docs for the supported
/// subset.
#[proc_macro_attribute]
pub fn verify(attr: TokenStream, item: TokenStream) -> TokenStream {
    let func = parse_macro_input!(item as ItemFn);
    // `#[verify(expect_bug)]` flips the generated `#[test]` to *assert a
    // counterexample is found* (and reproduces) instead of asserting verified —
    // so a known-buggy example is a passing demonstration in the test suite.
    let expect_bug = attr.to_string().contains("expect_bug");
    match parse::expand(&func, expect_bug) {
        Ok(tokens) => tokens.into(),
        Err(err) => {
            // Keep the original function so downstream errors are about the
            // unsupported construct, not "function not found".
            let original = &func;
            let compile_error = err.to_compile_error();
            quote! {
                #original
                #compile_error
            }
            .into()
        }
    }
}

/// `#[axeyum::unwind(K)]` is consumed by [`verify`] when it precedes a `for`/
/// `while`; as a standalone attribute it is an inert marker (returns the item
/// unchanged) so it type-checks on its own.
#[proc_macro_attribute]
pub fn unwind(_attr: TokenStream, item: TokenStream) -> TokenStream {
    item
}
