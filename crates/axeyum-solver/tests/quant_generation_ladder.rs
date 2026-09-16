//! The generation ladder on the quantifier loop's final refutation check
//! (ADR-2133, `AXEYUM_QINST_GEN_LADDER` / [`GenerationLadderGuard`]).
//!
//! **What the mechanism is.** When the e-matching loop gives up, the
//! accumulated ground set goes to one flat quantifier-free refutation check.
//! `qinst_egraph::finish_quantified_ground_check` puts one shallow pre-check in
//! front of it — the subset at instantiation generation
//! `FLOOD_FINAL_SUBSET_MAX_GENERATION = 1` — but only once the set has reached
//! `FLOOD_FINAL_SUBSET_CHECK_MIN_GROUND = 2048` terms. Measured on ADR-2113's
//! 53 reference-minimal `UFLIA` cores
//! (`bench-results/quant-instance-select-20260916/`), that pre-check does not
//! run on 26 of the 37 cores that leave a ground dump, because their sets have
//! a median of 1,061 terms; and where it does run it admits 69.5 % of them.
//! Against that, z3's own `:max-generation` needs generation `>= 3` on 25 of
//! the 53. Level 1 replaces the single fixed depth with an ascending ladder —
//! `gen <= 0`, `gen <= 1`, … — under one fractional budget, stopping at the
//! first layer that refutes.
//!
//! **Why no verdict this produces can be wrong, and what these tests therefore
//! aim at.** Every layer is a SUBSET of the conjunction the unchanged full
//! check already takes, and every member of that conjunction is an original
//! assertion or an admitted instance of an asserted universal. So a layer's
//! `unsat` refutes the whole set — the ladder is strictly additive, and can
//! only turn an `unknown` into an `unsat`. It never claims `sat`: a layer that
//! does not refute is discarded, not believed.
//!
//! That shape means the brief's suggested soundness-negative — "a `sat`
//! claimed before the lazy queue drains" — has no analogue here, because there
//! is no `sat` path to claim it on. The two failure modes this lever really
//! has are:
//!
//! 1. **A layer's non-refutation swallows the full check.** If
//!    `generation_ladder_check` returned a verdict instead of `None` when
//!    nothing refuted, a query only the FULL set refutes would come back
//!    `unknown`. That is what every `UNSAT_` fixture below is for, and it is
//!    exactly what makes them positive controls rather than decoration: a suite
//!    of satisfiable queries passes trivially against an engine that decides
//!    nothing.
//! 2. **A layer is not actually a subset.** If the filter admitted terms above
//!    its own layer, a layer could refute using facts the layer does not own —
//!    still sound here (it is all still a subset of `ground`), but it would
//!    destroy the ladder's reason to exist. Layer PRECISION is pinned where
//!    generations can be constructed exactly, in the unit tests
//!    `the_generation_ladder_refutes_at_the_shallowest_layer_that_can` and
//!    `a_ladder_that_refutes_nothing_must_not_swallow_the_full_check` in
//!    `qinst_egraph`; this file pins the end-to-end contract, where the
//!    generation of each conjunct is whatever the loop actually derived.
//!
//! Every fixture runs at BOTH levels. A fixture run only at the arm under test
//! cannot show that the shipped arm still agrees, and the shipped arm is what
//! a regression would break.

#![cfg(feature = "full")]

use std::time::Duration;

use axeyum_smtlib::parse_script;
use axeyum_solver::{
    CheckResult, GenerationLadderGuard, SolverConfig, prove_quantified_unsat_via_egraph,
};

/// Level 0 is the shipped arm; level 1 is the ladder. Both, always.
const LEVELS: [usize; 2] = [0, 1];

fn config() -> SolverConfig {
    SolverConfig {
        timeout: Some(Duration::from_secs(10)),
        ..SolverConfig::default()
    }
}

/// The E-matching refutation loop alone, so a verdict is attributable to the
/// ladder rather than to one of the front door's other routes.
///
/// **The guard is set on THIS thread and the loop runs on it**, which is the
/// only reason a guard can be used here — `GenerationLadderGuard` does not
/// cross a thread boundary, so the binary-level A/B uses `AXEYUM_QINST_GEN_LADDER`.
fn ematch_at(level: usize, text: &str) -> CheckResult {
    let _guard = GenerationLadderGuard::set(level);
    let mut script = parse_script(text).expect("parses");
    prove_quantified_unsat_via_egraph(&mut script.arena, &script.assertions, &config())
        .expect("no solver error")
}

// ---------------------------------------------------------------------------
// SOUNDNESS-NEGATIVE. A satisfiable query must not be refuted at either level.
// ---------------------------------------------------------------------------

/// A satisfiable `UFLIA` query whose satisfiability depends on the very
/// instances the loop derives: `f(a)` and `f(b)` may both be `5` with `a != b`,
/// so no subset of the ground set is unsatisfiable and no layer of the ladder
/// may claim otherwise.
const SAT_INSTANCES_ARE_CONSISTENT: &str = r"
(set-logic UFLIA)
(declare-fun f (Int) Int)
(declare-fun a () Int)
(declare-fun b () Int)
(assert (forall ((x Int)) (! (= (f x) 5) :pattern ((f x)))))
(assert (not (= a b)))
(assert (= (f a) 5))
(assert (= (f b) 5))
(check-sat)
";

/// Satisfiable, and deliberately built so the loop derives a CHAIN of
/// instances: `g` applied to an `f`-image is a term no source assertion
/// contains, so the instance that matches on it can only exist at a deeper
/// generation. Every layer of the ladder is therefore non-trivial, and every
/// one of them must decline to refute.
const SAT_DEEP_CHAIN_IS_CONSISTENT: &str = r"
(set-logic UFLIA)
(declare-sort U 0)
(declare-fun f (U) U)
(declare-fun g (U) U)
(declare-fun p (U) Bool)
(declare-fun a () U)
(assert (forall ((x U)) (! (= (f x) (g x)) :pattern ((f x)))))
(assert (forall ((y U)) (! (p (g y)) :pattern ((g y)))))
(assert (p (f a)))
(check-sat)
";

#[test]
fn a_satisfiable_query_is_not_refuted_at_either_level() {
    for level in LEVELS {
        for (name, text) in [
            ("SAT_INSTANCES_ARE_CONSISTENT", SAT_INSTANCES_ARE_CONSISTENT),
            ("SAT_DEEP_CHAIN_IS_CONSISTENT", SAT_DEEP_CHAIN_IS_CONSISTENT),
        ] {
            let result = ematch_at(level, text);
            assert_ne!(
                result,
                CheckResult::Unsat,
                "{name} is satisfiable but level {level} refuted it"
            );
        }
    }
}

// ---------------------------------------------------------------------------
// POSITIVE CONTROLS. Without these the file above passes against an engine
// that has stopped deciding anything at all -- and they are simultaneously the
// guard against a ladder that swallows the full check.
// ---------------------------------------------------------------------------

/// Refutable from instances bound on source terms alone. The shallow layers of
/// the ladder own this one outright.
const UNSAT_SHALLOW: &str = r"
(set-logic UFLIA)
(declare-fun f (Int) Int)
(declare-fun a () Int)
(assert (forall ((x Int)) (! (= (f x) 5) :pattern ((f x)))))
(assert (not (= (f a) 5)))
(check-sat)
";

/// **The fixture that dies if the ladder swallows the full check.** The
/// contradiction needs the instance at `g(a)` — a term no source assertion
/// contains, so it exists only because an earlier instance built it. A ladder
/// that refuses to fall through to the full check after its layers decline
/// returns `unknown` here.
const UNSAT_NEEDS_THE_DEEPER_INSTANCE: &str = r"
(set-logic UFLIA)
(declare-sort U 0)
(declare-fun f (U) U)
(declare-fun g (U) U)
(declare-fun p (U) Bool)
(declare-fun a () U)
(assert (forall ((x U)) (! (= (f x) (g x)) :pattern ((f x)))))
(assert (forall ((y U)) (! (p (g y)) :pattern ((g y)))))
(assert (p (f a)))
(assert (not (p (g a))))
(check-sat)
";

#[test]
fn an_unsatisfiable_query_is_still_refuted_at_both_levels() {
    for level in LEVELS {
        for (name, text) in [
            ("UNSAT_SHALLOW", UNSAT_SHALLOW),
            (
                "UNSAT_NEEDS_THE_DEEPER_INSTANCE",
                UNSAT_NEEDS_THE_DEEPER_INSTANCE,
            ),
        ] {
            assert_eq!(
                ematch_at(level, text),
                CheckResult::Unsat,
                "{name} must still be refuted at level {level}; a level that \
                 stops refuting makes the soundness-negative fixtures vacuous"
            );
        }
    }
}

/// The lever is OFF in the shipped configuration, and this test reads that from
/// the engine rather than from the constant: with no guard and no environment
/// override, the two levels must be distinguishable only by the guard, and the
/// unguarded run must agree with level 0.
#[test]
fn the_shipped_default_is_the_level_zero_arm() {
    assert!(
        std::env::var_os("AXEYUM_QINST_GEN_LADDER").is_none(),
        "this test measures the DEFAULT, so it cannot run under an override"
    );
    let mut script = parse_script(UNSAT_SHALLOW).expect("parses");
    let unguarded =
        prove_quantified_unsat_via_egraph(&mut script.arena, &script.assertions, &config())
            .expect("no solver error");
    assert_eq!(unguarded, ematch_at(0, UNSAT_SHALLOW));
    assert_eq!(unguarded, CheckResult::Unsat);
}
