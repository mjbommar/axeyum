//! The kernel's stack envelope: one documented size, one helper, one number
//! that a gate can measure.
//!
//! # Why this module exists
//!
//! Type checking a Lean term is recursive over the term, and this kernel is
//! directly recursive like Lean's own. Building a constructed carrier therefore
//! consumes stack proportional to the deepest proof term in it, and the default
//! **2 MiB** stack Rust gives a spawned thread (which is what a `#[test]` runs
//! on) is not enough. When it runs out the process aborts — `fatal runtime
//! error: stack overflow`, SIGABRT, **exit 134** — which is indistinguishable
//! from a broken tool or an absent declaration, and has been read as both.
//!
//! Before this module, eight call sites carried a verbatim copy of the same
//! thread-spawning helper at three different sizes (64 MiB ×5, 256 MiB ×3,
//! 1 GiB ×1), none of which was derived from a measurement. This is the one
//! copy and the one number.
//!
//! # The measurement behind [`DEEP_STACK_BYTES`]
//!
//! Measured 2026-08-26 by bisection: the smallest power-of-two thread stack on
//! which `examples/kernel_stack_envelope` completes each prelude's build. One
//! power of two lower, the process aborts. The full table and the gate that
//! re-derives it are `artifacts/kernel-stack-envelope.tsv` and
//! `scripts/check-kernel-stack-envelope.sh`.
//!
//! | prelude   |          debug |      release |
//! |-----------|---------------:|-------------:|
//! | `cpoint`  | **33,554,432** |    1,048,576 |
//! | `complex` |      4,194,304 |      262,144 |
//! | `creal`   |  **2,097,152** |      131,072 |
//! | `rat`     |      1,048,576 |      131,072 |
//! | `nat`     |        262,144 |       65,536 |
//! | `logic`   |        131,072 |      < 8,192 |
//!
//! Three things follow, and none of them was known before the numbers existed:
//!
//! - **`creal` in debug needs exactly 2,097,152 bytes — the default stack.**
//!   There was no margin at all, which is why one deep declaration (`CReal.e`)
//!   was enough to stop the axiom-freedom guard from running.
//! - **`cpoint` in debug needs 32 MiB**, so the five call sites that used a
//!   64 MiB thread had **2×** headroom, not the comfortable margin the number
//!   looks like. That is the finding that set this constant.
//! - **Debug costs up to 32× release for the same term** (cpoint: 33,554,432
//!   vs 1,048,576). The depth is identical in both; only the frames differ.
//!   That is the measured reason `prelude_theorem_inventory` must be run
//!   `--release`, and the measured reason a single recursion-*depth* limit
//!   cannot be calibrated once for both profiles.
//!
//! An earlier attempt at this table instrumented `infer_core`, `whnf_core`,
//! `def_eq_core_uncached` and `instantiate_aux` with a stack-pointer probe and
//! reported a `cpoint` peak of 1,681,616 B — **12× too small**, because a probe
//! sees only the frames it is installed in and the deepest recursion of the run
//! need not pass through any of them (`Kernel::abstract_aux` is recursive over
//! the term and was not instrumented). The bisection is the authoritative
//! number precisely because it measures the process rather than a chosen
//! subset of it. Do not replace it with an in-process probe.
//!
//! # What this is not
//!
//! It is **not** a limit. Nothing here makes the kernel refuse a term; the
//! kernel has no recursion-depth guard and returning one would be a change to
//! the trusted surface (see the ADR). This module only makes sure the stack the
//! recursion is given is a stated quantity rather than a per-file accident.
//!
//! # Do not use `RUST_MIN_STACK` instead
//!
//! A test that passes only under an ambient environment variable is a gate on
//! one shell. It has already happened here: a lane had `RUST_MIN_STACK`
//! exported from an earlier hand-bisect, reported a suite green, and the same
//! test aborted (`SIGABRT`) in a clean shell. Carry the stack explicitly.

/// The stack size every kernel routine that builds a constructed environment
/// runs on: **256 MiB**.
///
/// See the [module docs](self) for the measurement this is headroom over, and
/// `scripts/check-kernel-stack-envelope.sh` for the gate that re-derives it.
pub const DEEP_STACK_BYTES: usize = 256 * 1024 * 1024;

/// Run `f` on a thread with a [`DEEP_STACK_BYTES`] stack and return its value.
///
/// Panics if the thread cannot be spawned, and re-panics if `f` panicked, so a
/// failing assertion inside `f` still fails the test that called this.
///
/// ```
/// # use axeyum_lean_kernel::{Kernel, build_nat_prelude, on_a_deep_stack};
/// let names = on_a_deep_stack(|| {
///     let mut kernel = Kernel::new();
///     build_nat_prelude(&mut kernel).expect("nat prelude must build");
///     kernel.environment().iter().count()
/// });
/// assert!(names > 0);
/// ```
///
/// # Panics
///
/// If the deep-stack thread cannot be spawned, or if `f` panics.
pub fn on_a_deep_stack<T: Send + 'static>(f: impl FnOnce() -> T + Send + 'static) -> T {
    std::thread::Builder::new()
        .stack_size(DEEP_STACK_BYTES)
        .spawn(f)
        .expect("spawning a deep-stack thread must succeed")
        .join()
        .expect("the deep-stack thread must not panic")
}
