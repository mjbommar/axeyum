//! A Lean module too large to be useful must be REFUSED, not returned.
//!
//! `BvAlternationCounterexample` was returning `Ok` with a **2.38 GB** module
//! (`small-pipeline-fixpoint-3`) and **625 MB** (`bug802`), held as a single
//! `String`, on a box whose kernel OOM-killed a live agent session three days
//! earlier. Nothing downstream treats `Ok` as a hazard, so a route that succeeds
//! at that size is worse than one that declines.
//!
//! The cap is a measured threshold, not a guess: across the 262 modules the
//! committed dominance audits record a size for, the median is 3,169 bytes and
//! the largest legitimate one is 28.6 MB. 64 MiB is ~2x over that and 10x-37x
//! under the pathological pair — the two populations do not overlap.

#![cfg(feature = "full")]

use axeyum_smtlib::parse_script;
use axeyum_solver::{MAX_LEAN_MODULE_BYTES, prove_unsat_to_lean_module};

/// A small query that reconstructs normally: the cap must not disturb it.
const SMALL: &str = "(set-logic QF_LRA)\n\
     (declare-fun x () Real)\n\
     (assert (< x 0.0))\n(assert (<= 0.0 x))\n(check-sat)";

#[test]
fn an_ordinary_module_is_unaffected() {
    let mut parsed = parse_script(SMALL).expect("parses");
    let assertions = parsed.assertions.clone();
    let (_fragment, module) = prove_unsat_to_lean_module(&mut parsed.arena, &assertions)
        .expect("a small LRA refutation still reconstructs");
    assert!(!module.is_empty());
    assert!(
        module.len() < MAX_LEAN_MODULE_BYTES,
        "this fixture is meant to be far under the cap; it is {} bytes",
        module.len()
    );
}

/// The cap's own arithmetic, exercised without building a gigabyte.
///
/// The guard is a size comparison at the front door; constructing a real 2.4 GB
/// module to test it would cost more memory than the bug it guards. This pins
/// the boundary instead — and pins that the limit is the measured one, so
/// raising it silently past the largest observed real module (28.6 MB) fails
/// here.
#[test]
fn the_cap_sits_between_the_largest_real_module_and_the_pathological_ones() {
    // Reads the SHIPPED constant, not a copy: changing the cap must be able to
    // fail here. An earlier version hardcoded 64 MiB, so raising the limit would
    // have left this green while the threshold it documents moved.
    const LARGEST_REAL: usize = 28_634_049; // issue2031-bv-var-elim
    const SMALLEST_PATHOLOGICAL: usize = 625_781_636; // bug802

    // `const` assertions: these are facts about the constant, so the BUILD
    // should fail, not a test run. (Clippy flags a runtime `assert!` on
    // compile-time values, and it is right to.)
    const _: () = assert!(
        LARGEST_REAL < MAX_LEAN_MODULE_BYTES,
        "the cap must not reject a module the audits show is useful"
    );
    const _: () = assert!(
        MAX_LEAN_MODULE_BYTES < SMALLEST_PATHOLOGICAL,
        "the cap must reject the modules that motivated it"
    );
    // ...and the separation must stay wide enough that this is a threshold
    // rather than a coin flip: at least 2x either side.
    const _: () = assert!(LARGEST_REAL * 2 <= MAX_LEAN_MODULE_BYTES);
    const _: () = assert!(MAX_LEAN_MODULE_BYTES * 2 <= SMALLEST_PATHOLOGICAL);
}
