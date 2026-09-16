//! Incremental ground closure for quantifier instances: the retained CDCL(T)
//! session hosting a ground set with arithmetic in it (ADR-2124,
//! `AXEYUM_QINST_GROUND_SESSION` / [`GroundSessionLevelGuard`]).
//!
//! **What the mechanism is.** The instantiation loop's interleaved ground check
//! fires behind ONE gate — `online_clauses.is_none()` in
//! `qinst_egraph::prove_quantified_unsat_via_egraph_impl`. When the retained
//! session exists, the loop updates it; when it does not, every due round
//! re-solves the WHOLE accumulated ground set from scratch. At the shipped level
//! the session refuses any ground set holding a Boolean-position term its `EUF`
//! encoder has no arm for — an integer comparison is one — so on `UFLIA` the
//! session never exists and the loop is in the re-solve regime for its whole
//! run. Measured on ADR-2120's 53 reference-minimal `UFLIA` cores: 493 cold
//! checks over sets of up to 8,019 terms, 33 of 53 dying on the clock.
//!
//! Level 1 abstracts that term to a free propositional variable, so the session
//! exists and the loop asserts instances into it instead. Neither reference
//! solver re-solves the ground part either: z3 internalizes the instance clause
//! into the live `smt::context` (`src/smt/qi_queue.cpp:336` →
//! `src/smt/smt_context.h:1781` → `src/smt/smt_internalizer.cpp:1460`) and
//! simply continues the same search (`src/smt/smt_context.cpp:4174`); cvc5 sends
//! it as a lemma into the running prop engine
//! (`src/theory/quantifiers/instantiate.cpp:339` →
//! `src/theory/theory_engine.cpp:1659`).
//!
//! **Soundness is an abstraction argument and these tests do not establish it —
//! they try to REFUTE it.** Replacing an atom by a free propositional variable
//! only ADDS models: every model of the original extends to one of the skeleton
//! by giving the variable the atom's truth value. So the skeleton is WEAKER, an
//! `unsat` of it transfers back, and a `sat` of it says nothing. If the
//! abstraction could manufacture a refutation, it would be on a SATISFIABLE
//! query whose satisfiability depends on the very atoms that were abstracted —
//! which is what every `SAT_` fixture below is.
//!
//! There is a second, independent reason no session verdict can be wrong, and
//! it is worth stating because it is what makes level 1 shippable rather than
//! merely arguable: the session's `Unsat` is **never the verdict**.
//! `scoped_candidate_fixpoint_step` reaches `Refuted` only through
//! `replay_online_refutation`, which re-establishes the refutation over the same
//! ground set with the ordinary cold quantifier-free route. The session picks
//! WHEN to look; the cold route still says whether the refutation is real.
//!
//! **The positive controls matter as much as the negatives.** A suite of
//! satisfiable queries passes trivially against an engine that decides nothing,
//! so `UNSAT_` fixtures below require a refutation at BOTH levels — otherwise
//! this file would go green on a level 1 that had quietly stopped working.

#![cfg(feature = "full")]

use std::time::Duration;

use axeyum_smtlib::parse_script;
use axeyum_solver::{
    CheckResult, GroundSessionLevelGuard, SolverConfig, prove_quantified_unsat_via_egraph,
};

/// Level 0 is the shipped arm; level 1 is what ADR-2124 measures. Every fixture
/// runs at BOTH, because a fixture run only at the arm under test cannot show
/// that the shipped arm still agrees.
const LEVELS: [usize; 2] = [0, 1];

fn config() -> SolverConfig {
    SolverConfig {
        timeout: Some(Duration::from_secs(10)),
        ..SolverConfig::default()
    }
}

/// The E-matching refutation loop alone, so a verdict is attributable to the
/// ground session rather than to one of the front door's other routes.
///
/// **The guard is set on THIS thread and the loop runs on it**, which is the
/// only reason a guard can be used here at all — `GroundSessionLevelGuard` does
/// not cross a thread boundary, so the binary-level A/B uses the environment
/// variable instead.
fn ematch_at(level: usize, text: &str) -> CheckResult {
    let _guard = GroundSessionLevelGuard::set(level);
    let mut script = parse_script(text).expect("parses");
    prove_quantified_unsat_via_egraph(&mut script.arena, &script.assertions, &config())
        .expect("no solver error")
}

// ---------------------------------------------------------------------------
// SOUNDNESS-NEGATIVE. A satisfiable query must not be refuted at any level.
// ---------------------------------------------------------------------------

/// **THE fixture this lane's abstraction aims at.**
///
/// `f(a) < 10` and `f(b) < 10` are the instances the trigger produces, and they
/// are exactly the atoms level 1 abstracts — the session sees two unrelated free
/// variables where the cold route sees two integer comparisons. The query is
/// SATISFIABLE (take `f` constantly `0`, `a = b = 0`, `g` constantly `0`), so
/// any `unsat` is manufactured.
///
/// It is refuted by an abstraction that is not a weakening: one that, say,
/// asserted the abstracted variable TRUE on the strength of the comparison's
/// syntactic shape, or that collapsed `f(a) < 10` with `¬(f(a) < 10)` onto one
/// polarity. Both are ordinary off-by-one mistakes in an abstraction layer and
/// both refute this.
const SAT_ABSTRACTED_COMPARISONS: &str = r"
    (set-logic UFLIA)
    (declare-fun f (Int) Int)
    (declare-fun g (Int) Int)
    (declare-const a Int)
    (declare-const b Int)
    (assert (forall ((x Int)) (< (f x) 10)))
    (assert (= (g a) (g b)))
    (assert (< a 10))
    (assert (< b 10))
    (check-sat)
";

/// Two DISTINCT comparisons that a careless abstraction would collapse.
///
/// `(< a 1)` and `(< b 1)` are different terms with different truth values in
/// the intended model: `a = 0` makes the first true, `b = 5` makes the second
/// false, and `(not (< b 1))` is asserted. An abstraction keyed on anything
/// coarser than the hash-consed `TermId` — the operator, the sort, the
/// right-hand constant — maps both to one variable and the query becomes
/// `v ∧ ¬v`, refuted.
///
/// The `EUF` equality is there so the session is not declined for having no
/// theory atom at all; without it this fixture would pass by never building a
/// session.
const SAT_DISTINCT_COMPARISONS_NOT_COLLAPSED: &str = r"
    (set-logic UFLIA)
    (declare-fun h (Int) Int)
    (declare-const a Int)
    (declare-const b Int)
    (assert (= (h a) (h a)))
    (assert (< a 1))
    (assert (not (< b 1)))
    (assert (forall ((x Int)) (>= (h x) 0)))
    (check-sat)
";

/// A satisfiable query whose universal is instantiated many times, so the
/// session accumulates clauses across several rounds.
///
/// This is the shape that exercises the session's ROOT-LEVEL insertion
/// discipline end to end: each round's instances are inserted after the previous
/// solve has put decisions on the trail. A session that inserted under a live
/// trail would record a fact holding only under those decisions and keep it
/// after the next backjump — the stale-clause hazard — and a stale clause on a
/// satisfiable query is a manufactured `unsat`.
const SAT_MANY_ROUNDS: &str = r"
    (set-logic UFLIA)
    (declare-fun f (Int) Int)
    (declare-const a Int)
    (declare-const b Int)
    (declare-const c Int)
    (assert (forall ((x Int)) (<= (f x) (f (+ x 1)))))
    (assert (= (f a) (f b)))
    (assert (<= (f a) (f c)))
    (assert (>= a 0))
    (check-sat)
";

// ---------------------------------------------------------------------------
// POSITIVE CONTROLS. A refutable query must still be refuted at BOTH levels.
// ---------------------------------------------------------------------------

/// An `EUF` refutation that needs no arithmetic: the universal forces
/// `f(a) = c`, and `f(a) ≠ c` is asserted. Both levels must refute it.
///
/// Its job is to fail if level 1 ever stops refuting — which a suite of
/// satisfiable fixtures alone could never notice.
const UNSAT_EUF_INSTANCE: &str = r"
    (set-logic UFLIA)
    (declare-fun f (Int) Int)
    (declare-const a Int)
    (declare-const c Int)
    (assert (forall ((x Int)) (= (f x) c)))
    (assert (not (= (f a) c)))
    (check-sat)
";

/// The same, with an integer comparison in the ground set — so at level 1 this
/// query goes through a session that EXISTS, and at level 0 through one that was
/// declined. The refutation is still `EUF`, so both must reach it.
const UNSAT_EUF_INSTANCE_BESIDE_ARITHMETIC: &str = r"
    (set-logic UFLIA)
    (declare-fun f (Int) Int)
    (declare-const a Int)
    (declare-const c Int)
    (assert (< a 10))
    (assert (forall ((x Int)) (= (f x) c)))
    (assert (not (= (f a) c)))
    (check-sat)
";

// ---------------------------------------------------------------------------
// The assertions.
// ---------------------------------------------------------------------------

#[test]
fn a_satisfiable_query_is_never_refuted_at_either_level() {
    for (name, text) in [
        ("SAT_ABSTRACTED_COMPARISONS", SAT_ABSTRACTED_COMPARISONS),
        (
            "SAT_DISTINCT_COMPARISONS_NOT_COLLAPSED",
            SAT_DISTINCT_COMPARISONS_NOT_COLLAPSED,
        ),
        ("SAT_MANY_ROUNDS", SAT_MANY_ROUNDS),
    ] {
        for level in LEVELS {
            assert_ne!(
                ematch_at(level, text),
                CheckResult::Unsat,
                "{name} is SATISFIABLE; a refutation at level {level} is a wrong `unsat`"
            );
        }
    }
}

#[test]
fn a_refutable_query_is_still_refuted_at_level_1() {
    for (name, text) in [
        ("UNSAT_EUF_INSTANCE", UNSAT_EUF_INSTANCE),
        (
            "UNSAT_EUF_INSTANCE_BESIDE_ARITHMETIC",
            UNSAT_EUF_INSTANCE_BESIDE_ARITHMETIC,
        ),
    ] {
        for level in LEVELS {
            assert_eq!(
                ematch_at(level, text),
                CheckResult::Unsat,
                "{name} must be refuted at level {level}; a suite of satisfiable \
                 fixtures alone would not notice level 1 deciding nothing"
            );
        }
    }
}

/// The two levels may differ in TIME and in how often they answer `unknown`.
/// They may never differ in a DECIDED verdict.
///
/// This is the whole ship gate written as an assertion: a flip here is a
/// soundness defect on one of the two arms, and which one does not matter.
#[test]
fn the_two_levels_never_disagree_on_a_decided_verdict() {
    let mut compared = 0usize;
    for text in [
        SAT_ABSTRACTED_COMPARISONS,
        SAT_DISTINCT_COMPARISONS_NOT_COLLAPSED,
        SAT_MANY_ROUNDS,
        UNSAT_EUF_INSTANCE,
        UNSAT_EUF_INSTANCE_BESIDE_ARITHMETIC,
    ] {
        let off = ematch_at(0, text);
        let on = ematch_at(1, text);
        let decided = |r: &CheckResult| !matches!(r, CheckResult::Unknown(_));
        if decided(&off) && decided(&on) {
            compared += 1;
            assert_eq!(
                off, on,
                "level 0 and level 1 decided the same query differently"
            );
        }
    }
    // A comparison count of zero would mean this test compared NOTHING and
    // passed anyway -- the vacuous shape a differential is most prone to.
    assert!(
        compared >= 2,
        "the differential compared only {compared} decided pairs; it is not \
         exercising the arms it claims to compare"
    );
}
