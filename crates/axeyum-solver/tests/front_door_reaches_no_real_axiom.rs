//! **The shipped front door never builds the `Real` axiom package.**
//!
//! # The gap this closes
//!
//! Every claim so far that a route no longer depends on the axiomatized `Real`
//! carrier has been checked by reading the finished proof term's axiom
//! footprint — `examples/front_door_carrier.rs --require-axiom-free`,
//! `examples/ordered_ring_refutation.rs --require-empty`, and the payoff tests
//! in `signature_tests`. That is the right check for a *term*. It is not the
//! same question as whether the route **reached** the axioms, and the two
//! answers were different:
//!
//! `reconstruct_int_farkas_to_lean_module` — the `ProofFragment::IntFarkas`
//! arm of `prove_unsat_to_lean_module`, and a shipped route — built the `Real`
//! package, refuted there, abstracted all 30 constants back out with
//! `generalize_over_ordered_ring`, and instantiated at `ℤ`. Its module named no
//! `Real` axiom and its footprint was empty, so every footprint-shaped check
//! passed while the route constructed the entire trusted surface to get there.
//! `front_door_carrier` could not see it either: its three fixtures are all
//! real-typed, so they route to `Lra` and `Sos` and never reach the integer
//! arm. An empty result from a tool that was never pointed at the subject.
//!
//! # What this measures instead
//!
//! `axeyum_lean_kernel::arith_prelude_builds()` counts calls to
//! `build_arith_prelude` in this process. Zero after driving the front door is
//! a strictly stronger statement than an empty footprint: it says the axioms
//! were never declared into any kernel this route touched, so no later change
//! to the abstraction machinery can quietly reintroduce a dependency on them.
//!
//! # One test, deliberately
//!
//! The counter is process-global. A second `#[test]` in this binary that built
//! the package — including the negative control below — would run concurrently
//! with this one and make the reading meaningless. So this file has exactly one
//! test, and the control lives inside it, after the measurement.

#![cfg(feature = "full")]

use axeyum_ir::{Rational, TermArena, TermId};
use axeyum_lean_kernel::arith_prelude_builds;
use axeyum_solver::{LraReconstructCtx, ProofFragment, prove_unsat_to_lean_module};

/// `x < 0 ∧ 0 ≤ x` — the two-row strict conflict. Routes to `Lra`.
fn strict_bound_conflict(arena: &mut TermArena) -> Vec<TermId> {
    let x = arena.real_var("x").unwrap();
    let zero = arena.real_const(Rational::integer(0));
    vec![
        arena.real_lt(x, zero).unwrap(),
        arena.real_le(zero, x).unwrap(),
    ]
}

/// `x·x < 0` — the sum-of-squares route, the only one that touches the
/// multiplicative laws and `sq_nonneg`.
fn sos_square(arena: &mut TermArena) -> Vec<TermId> {
    let x = arena.real_var("x").unwrap();
    let zero = arena.real_const(Rational::integer(0));
    let sq = arena.real_mul(x, x).unwrap();
    vec![arena.real_lt(sq, zero).unwrap()]
}

/// `x ≤ 0 ∧ y ≤ 0 ∧ (x ≥ 1 ∨ y ≥ 1)` — the `Or.rec` case split.
fn disjunctive_case_split(arena: &mut TermArena) -> Vec<TermId> {
    let x = arena.real_var("x").unwrap();
    let y = arena.real_var("y").unwrap();
    let zero = arena.real_const(Rational::integer(0));
    let one = arena.real_const(Rational::integer(1));
    let x_le_0 = arena.real_le(x, zero).unwrap();
    let y_le_0 = arena.real_le(y, zero).unwrap();
    let x_ge_1 = arena.real_ge(x, one).unwrap();
    let y_ge_1 = arena.real_ge(y, one).unwrap();
    let clause = arena.or(x_ge_1, y_ge_1).unwrap();
    vec![x_le_0, y_le_0, clause]
}

/// `5 < x ∧ x < 3` over `Int` — the integer Farkas arm, and the one that used
/// to build all 30 axioms.
fn integer_farkas(arena: &mut TermArena) -> Vec<TermId> {
    let x = arena.int_var("x").unwrap();
    let five = arena.int_const(5);
    let three = arena.int_const(3);
    vec![
        arena.int_lt(five, x).unwrap(),
        arena.int_lt(x, three).unwrap(),
    ]
}

#[test]
fn the_shipped_front_door_never_builds_the_real_axiom_package() {
    assert_eq!(
        arith_prelude_builds(),
        0,
        "something built the Real package before this test ran; the reading below would \
         not be about the front door"
    );

    type Fixture = (
        &'static str,
        ProofFragment,
        fn(&mut TermArena) -> Vec<TermId>,
    );
    let fixtures: &[Fixture] = &[
        (
            "lra          x<0 and 0<=x",
            ProofFragment::Lra,
            strict_bound_conflict,
        ),
        ("sos          x*x<0", ProofFragment::Sos, sos_square),
        (
            "disjunctive  x<=0, y<=0, (x>=1 or y>=1)",
            ProofFragment::DisjunctiveLra,
            disjunctive_case_split,
        ),
        (
            "int-farkas   5<x and x<3 over Int",
            ProofFragment::IntFarkas,
            integer_farkas,
        ),
    ];

    for &(label, expected, build) in fixtures {
        let mut arena = TermArena::new();
        let assertions = build(&mut arena);
        let (fragment, source) = prove_unsat_to_lean_module(&mut arena, &assertions)
            .unwrap_or_else(|e| panic!("{label}: the front door declined: {e}"));

        // Pinned, because the whole point is coverage: a fixture that silently
        // stopped routing to the arm it is named for would leave that arm
        // unmeasured while this test kept passing.
        assert_eq!(
            fragment, expected,
            "{label} no longer routes to the arm this fixture exists to cover"
        );
        assert!(
            !source.contains("axiom Real : Sort"),
            "{label}: the emitted module declares the axiomatized Real carrier"
        );
        assert!(
            !source.contains("sorryAx"),
            "{label}: the emitted module contains `sorryAx`"
        );
        let builds = arith_prelude_builds();
        // Printed before it is asserted, so `--nocapture` carries the
        // measurement itself and not just a pass/fail. Fact evidence anchors on
        // these lines.
        println!(
            "FRONT_DOOR_REACH {label} | fragment={fragment:?} module={} arith_prelude_builds={builds}",
            source.len()
        );
        assert_eq!(
            builds, 0,
            "{label}: the shipped front door built the Real axiom package. Its module can \
             still be footprint-clean -- the IntFarkas arm abstracted the 30 constants back \
             out and instantiated at Z -- and that is exactly the failure this counter \
             exists to see."
        );
    }

    // The control, and the reason the four zeros above are worth reading: the
    // counter does move. Without this an `arith_prelude_builds` that had been
    // wired to a constant would pass every assertion in this test.
    let _real = LraReconstructCtx::try_new().expect("the Real package still builds");
    let after_control = arith_prelude_builds();
    println!("FRONT_DOOR_REACH control | arith_prelude_builds={after_control}");
    assert_eq!(
        after_control, 1,
        "the build counter did not move when the Real package was built on purpose, so the \
         zeros above measure nothing"
    );
}
