//! Soundness-floor helpers: confirm a reported counterexample actually makes the
//! *original* Rust function panic/overflow.
//!
//! No external tool is involved (Kani is not installed in this environment): the
//! independent ground truth is the original function itself, run on the witness
//! inputs. The macro-generated reproduction test calls the original fn inside
//! [`panics_on`]; a witness that does not panic is a lowering defect to fix, not
//! a finding to report (DISAGREE = 0).

use std::panic::{AssertUnwindSafe, catch_unwind};

/// Runs `f` (a closure that calls the original function on the witness inputs)
/// and returns `true` iff it panics. Panic output is suppressed for clean test
/// logs.
///
/// Used by the macro-generated reproduction `#[test]`: it asserts
/// `panics_on(|| original(witness...))` so a non-reproducing counterexample
/// fails the build.
#[must_use]
pub fn panics_on<F: FnOnce()>(f: F) -> bool {
    let prev = std::panic::take_hook();
    std::panic::set_hook(Box::new(|_| {}));
    let result = catch_unwind(AssertUnwindSafe(f));
    std::panic::set_hook(prev);
    result.is_err()
}
