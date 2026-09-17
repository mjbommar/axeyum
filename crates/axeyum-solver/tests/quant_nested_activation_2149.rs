//! Nested-binder activation (ADR-2149): what the e-matching loop does with a
//! universal that sits INSIDE another universal's body, step by step.
//!
//! **The question these fixtures decide.** QUANT-COMPOSE read the source and
//! concluded that no activation reaches a universal nested inside another
//! universal's binder: `collect_nested_registrations_rec` drops polarity
//! tracking on entering a `forall` body before any lever level is consulted,
//! so the registration has no `PositiveContext`, and its matched tuples are
//! discarded at the `inactive_dropped` site. z3 and cvc5 get the nested case
//! for free by asserting the instance back into the SAT layer, where the
//! exposed `forall` acquires its own handle.
//!
//! **What the fixtures show, read from counters and not from a verdict.**
//! The STATIC registration of a crossed-binder universal is indeed inert and
//! its tuples are indeed dropped — `dropped_crossed_binder` is nonzero on the
//! crossed fixtures and equals `dropped`. But that registration is not the
//! only handle the engine holds on the inner universal: `NestedDiscovery::scan`
//! re-walks every ADMITTED INSTANCE and every STAGED REPLACEMENT for
//! universals at positive positions and registers them against the instance
//! as owner — the reference solvers' mechanism, already built. The crossed
//! fixtures refute through THAT registration (`discovered >= 2`,
//! `handed_off >= 1`) at level 1, and at level 0 whenever the path is
//! `and`/`or` only. So the reading holds for the static registration and
//! fails for the engine.
//!
//! **What still blocks at level 0.** The brief's own fixture (a), with the
//! inner universal under `=>` in the outer's matrix, is `unknown` through the
//! isolated loop at the shipped level: its one registration is
//! `inert_untracked` (the `=>` step is refused at level 0, ADR-2120), matched
//! 14 tuples, and dropped all 14 as `rej_nocontext` — none of them
//! crossed-binder. The front door refutes the same text at level 0 because
//! its normalisation turns `=>` into `or`/`not` and the path is then
//! `or`-only. That is a level-0 whitelist fact, not a binder fact.
//!
//! Every counter is read through [`NestedActivationStatsGuard`], which arms
//! the loop's admission census in-process; a fixture that asserted only a
//! verdict could not tell "activated and refuted" from "refuted by another
//! route", and one that asserted only a registration count could not tell
//! "registered and dropped" from "registered and handed off".

#![cfg(feature = "full")]

use std::time::Duration;

use axeyum_smtlib::parse_script;
use axeyum_solver::{
    CheckResult, NestedActivationLevelGuard, NestedActivationStats, NestedActivationStatsGuard,
    PositivePathLevelGuard, QuantifierGroundDerivation, SolverConfig,
    check_quantifier_ground_derivation, last_nested_activation_stats,
    prove_quantified_unsat_via_egraph, prove_quantified_unsat_via_egraph_with_instances,
    solve_smtlib,
};

/// Level 0 is the shipped arm of ADR-2120's lever; level 1 is its ON arm.
const LEVELS: [usize; 2] = [0, 1];

fn config() -> SolverConfig {
    SolverConfig {
        timeout: Some(Duration::from_secs(10)),
        ..SolverConfig::default()
    }
}

/// The E-matching refutation loop alone, with the nested-activation counters
/// read back, so a verdict is attributable to the registration mechanism and
/// not to one of the front door's other routes.
fn ematch(text: &str) -> (CheckResult, NestedActivationStats) {
    let _stats = NestedActivationStatsGuard::enable();
    let mut script = parse_script(text).expect("parses");
    let verdict =
        prove_quantified_unsat_via_egraph(&mut script.arena, &script.assertions, &config())
            .expect("no solver error");
    (verdict, last_nested_activation_stats())
}

/// The shipped front door, counters included.
fn front_door(text: &str) -> (CheckResult, NestedActivationStats) {
    let _stats = NestedActivationStatsGuard::enable();
    let outcome = solve_smtlib(text, &config()).expect("no solver error");
    (outcome.result, last_nested_activation_stats())
}

fn at_level<T>(level: usize, run: impl FnOnce() -> T) -> T {
    let _guard = PositivePathLevelGuard::set(level);
    run()
}

// ---------------------------------------------------------------------------
// Fixtures. Every UNSAT one has a SAT twin that differs in one literal's
// polarity, so a wrong refutation has somewhere to show up.
// ---------------------------------------------------------------------------

/// (a) The brief's fixture: the inner universal sits under `=>` in the outer
/// universal's MATRIX — below the outer prefix, but not below a crossed
/// binder, because the outer prefix is peeled before the walk starts
/// (ADR-2120 §1a). UNSAT: `P(a)` forces `∀y. Q(a, y)`, against `¬Q(a, b)`.
const NESTED_UNDER_IMPLIES_UNSAT: &str = r"
    (set-logic UF)
    (declare-sort U 0)
    (declare-fun P (U) Bool)
    (declare-fun Q (U U) Bool)
    (declare-const a U)
    (declare-const b U)
    (assert (forall ((x U)) (=> (P x) (forall ((y U)) (Q x y)))))
    (assert (P a))
    (assert (not (Q a b)))
    (check-sat)
";

/// (a') SAT twin: `¬P(a)` discharges the implication, so `Q` is unconstrained.
const NESTED_UNDER_IMPLIES_SAT: &str = r"
    (set-logic UF)
    (declare-sort U 0)
    (declare-fun P (U) Bool)
    (declare-fun Q (U U) Bool)
    (declare-const a U)
    (declare-const b U)
    (assert (forall ((x U)) (=> (P x) (forall ((y U)) (Q x y)))))
    (assert (not (P a)))
    (assert (not (Q a b)))
    (check-sat)
";

/// (b) The positive control: the same statement with a FLAT prefix. Nothing
/// is nested, nothing is registered, and both levels must refute it.
const FLAT_PREFIX_UNSAT: &str = r"
    (set-logic UF)
    (declare-sort U 0)
    (declare-fun P (U) Bool)
    (declare-fun Q (U U) Bool)
    (declare-const a U)
    (declare-const b U)
    (assert (forall ((x U) (y U)) (=> (P x) (Q x y))))
    (assert (P a))
    (assert (not (Q a b)))
    (check-sat)
";

/// (c) A universal under a CROSSED binder: the innermost `∀y` is inside the
/// BODY of `∀u`, which is itself nested in `∀x`'s matrix. The static walk
/// registers `∀y` without a context (the path crosses `∀u`). UNSAT: `P(a)`
/// gives `∀u. (R(a,u) => ∀y. Q(u,y))`, `R(a,c)` gives `∀y. Q(c,y)`, against
/// `¬Q(c,b)`.
const CROSSED_BINDER_UNSAT: &str = r"
    (set-logic UF)
    (declare-sort U 0)
    (declare-fun P (U) Bool)
    (declare-fun R (U U) Bool)
    (declare-fun Q (U U) Bool)
    (declare-const a U)
    (declare-const b U)
    (declare-const c U)
    (assert (forall ((x U)) (=> (P x) (forall ((u U)) (=> (R x u) (forall ((y U)) (Q u y)))))))
    (assert (P a))
    (assert (R a c))
    (assert (not (Q c b)))
    (check-sat)
";

/// (c') SAT twin: `¬R(a,c)` discharges the middle implication.
const CROSSED_BINDER_SAT: &str = r"
    (set-logic UF)
    (declare-sort U 0)
    (declare-fun P (U) Bool)
    (declare-fun R (U U) Bool)
    (declare-fun Q (U U) Bool)
    (declare-const a U)
    (declare-const b U)
    (declare-const c U)
    (assert (forall ((x U)) (=> (P x) (forall ((u U)) (=> (R x u) (forall ((y U)) (Q u y)))))))
    (assert (P a))
    (assert (not (R a c)))
    (assert (not (Q c b)))
    (check-sat)
";

/// (d) The crossed-binder shape written with `or`/`not` instead of `=>`, so
/// the path to the middle universal is `or`-only and level 0 tracks it. The
/// only thing left untracked is the binder crossing itself.
const CROSSED_BINDER_OR_UNSAT: &str = r"
    (set-logic UF)
    (declare-sort U 0)
    (declare-fun P (U) Bool)
    (declare-fun R (U U) Bool)
    (declare-fun Q (U U) Bool)
    (declare-const a U)
    (declare-const b U)
    (declare-const c U)
    (assert (forall ((x U)) (or (not (P x)) (forall ((u U)) (or (not (R x u)) (forall ((y U)) (Q u y)))))))
    (assert (P a))
    (assert (R a c))
    (assert (not (Q c b)))
    (check-sat)
";

/// (d') SAT twin of (d).
const CROSSED_BINDER_OR_SAT: &str = r"
    (set-logic UF)
    (declare-sort U 0)
    (declare-fun P (U) Bool)
    (declare-fun R (U U) Bool)
    (declare-fun Q (U U) Bool)
    (declare-const a U)
    (declare-const b U)
    (declare-const c U)
    (assert (forall ((x U)) (or (not (P x)) (forall ((u U)) (or (not (R x u)) (forall ((y U)) (Q u y)))))))
    (assert (P a))
    (assert (not (R a c)))
    (assert (not (Q c b)))
    (check-sat)
";

/// (e) A universal at a NEGATIVE position inside the outer's matrix:
/// `¬∀y. Q(x,y)` is an existential, so nothing may be replaced. SAT: `¬P(a)`
/// forces some `y` to fail `Q(a, ·)`, and `Q(a, b)` says `b` is not that one.
/// This is what puts a nonzero in the `negative` class of the split.
const NEGATIVE_POSITION_SAT: &str = r"
    (set-logic UF)
    (declare-sort U 0)
    (declare-fun P (U) Bool)
    (declare-fun Q (U U) Bool)
    (declare-const a U)
    (declare-const b U)
    (assert (forall ((x U)) (or (P x) (not (forall ((y U)) (Q x y))))))
    (assert (not (P a)))
    (assert (Q a b))
    (check-sat)
";

const SAT_FIXTURES: [(&str, &str); 4] = [
    ("NESTED_UNDER_IMPLIES_SAT", NESTED_UNDER_IMPLIES_SAT),
    ("CROSSED_BINDER_SAT", CROSSED_BINDER_SAT),
    ("CROSSED_BINDER_OR_SAT", CROSSED_BINDER_OR_SAT),
    ("NEGATIVE_POSITION_SAT", NEGATIVE_POSITION_SAT),
];

const UNSAT_FIXTURES: [(&str, &str); 4] = [
    ("NESTED_UNDER_IMPLIES_UNSAT", NESTED_UNDER_IMPLIES_UNSAT),
    ("FLAT_PREFIX_UNSAT", FLAT_PREFIX_UNSAT),
    ("CROSSED_BINDER_UNSAT", CROSSED_BINDER_UNSAT),
    ("CROSSED_BINDER_OR_UNSAT", CROSSED_BINDER_OR_UNSAT),
];

// ---------------------------------------------------------------------------
// Deliverable 1(a): the brief's fixture, step by step, at the shipped level.
// ---------------------------------------------------------------------------

/// At level 0 the inner universal of (a) is REGISTERED (1), MATCHED (tuples
/// joined), and every tuple is DROPPED at the `inactive_dropped` site — and
/// the class of the drop is `untracked` (the `=>` step), NOT crossed-binder.
/// The verdict is `unknown`. This is the step-by-step account the brief asked
/// for, and each step is a counter rather than a reading.
#[test]
fn the_brief_fixture_is_registered_matched_and_dropped_untracked_at_level_0() {
    let (verdict, stats) = at_level(0, || ematch(NESTED_UNDER_IMPLIES_UNSAT));
    assert!(
        !matches!(verdict, CheckResult::Unsat),
        "level 0 refuted the brief's fixture through the isolated loop: the \
         shipped whitelist does not track `=>`, so if this refutes, some route \
         other than the one under test did it ({verdict:?})"
    );
    assert_eq!(stats.registrations, 1, "one nested universal is registered");
    assert_eq!(
        stats.with_context, 0,
        "level 0 gave the `=>`-nested universal a context; that is level 1's rule"
    );
    assert_eq!(
        stats.inert_untracked, 1,
        "the registration's first refusal is the `=>` connective ({stats:?})"
    );
    assert_eq!(
        stats.inert_crossed_binder, 0,
        "the brief's fixture has NO crossed binder: the outer prefix is peeled \
         before the walk, so the inner universal is in the outer's matrix"
    );
    assert!(
        stats.joined > 0,
        "the registration never matched, so 'dropped' below would be vacuous"
    );
    assert_eq!(
        stats.handed_off, 0,
        "nothing is handed off without a context"
    );
    assert_eq!(
        stats.dropped, stats.joined,
        "every joined tuple is dropped at the inactive_dropped site"
    );
    assert_eq!(
        stats.dropped_untracked, stats.dropped,
        "the drop is charged to the untracked (connective) class"
    );
    assert_eq!(
        stats.discovered, 0,
        "no instance is scanned into a registration"
    );
}

/// At level 1 the same fixture refutes, and the counters say HOW: the
/// registration has a context, its tuples are handed off, the instance of the
/// outer universal is scanned and yields a discovered registration, and a
/// binder-free replacement is staged into the ground set.
#[test]
fn the_brief_fixture_is_activated_and_refuted_at_level_1() {
    let (verdict, stats) = at_level(1, || ematch(NESTED_UNDER_IMPLIES_UNSAT));
    assert!(
        matches!(verdict, CheckResult::Unsat),
        "level 1 did not refute the brief's fixture ({verdict:?}, {stats:?})"
    );
    assert!(
        stats.with_context >= 1,
        "the registration carries a context"
    );
    assert!(
        stats.handed_off >= 1,
        "at least one tuple was handed off ({stats:?})"
    );
    assert!(
        stats.discovered >= 1,
        "the outer instance was not scanned into a registration ({stats:?})"
    );
    assert!(
        stats.staged_ground >= 1,
        "no replacement reached the ground set"
    );
    assert_eq!(
        stats.dropped, 0,
        "nothing is dropped at level 1 on this shape"
    );
}

// ---------------------------------------------------------------------------
// Deliverable 1(b): the flat positive control.
// ---------------------------------------------------------------------------

#[test]
fn the_flat_prefix_control_refutes_at_both_levels_with_no_registration() {
    for level in LEVELS {
        let (verdict, stats) = at_level(level, || ematch(FLAT_PREFIX_UNSAT));
        assert!(
            matches!(verdict, CheckResult::Unsat),
            "level {level}: the FLAT control was not refuted -- the harness \
             cannot refute anything, so every nested assertion is vacuous"
        );
        assert_eq!(
            stats.registrations, 0,
            "level {level}: a flat prefix registered a nested universal"
        );
        assert_eq!(
            stats.invocations, 1,
            "level {level}: the loop did not run once, so the zero above is not \
             a measurement of it"
        );
    }
}

// ---------------------------------------------------------------------------
// The crossed-binder shape, which the brief's fixture does not exercise.
// ---------------------------------------------------------------------------

/// The reading's strong form — "no activation reaches a universal inside
/// another binder" — is refuted here. The static registration IS inert and
/// its tuples ARE dropped (`dropped_crossed_binder == dropped > 0`); the
/// refutation comes through the registrations discovery adds from the
/// enclosing universal's instance and the staged replacement (`discovered >= 2`).
const CROSSED_CASES: [(&str, &str, usize); 3] = [
    ("CROSSED_BINDER_UNSAT", CROSSED_BINDER_UNSAT, 1),
    ("CROSSED_BINDER_OR_UNSAT", CROSSED_BINDER_OR_UNSAT, 0),
    ("CROSSED_BINDER_OR_UNSAT", CROSSED_BINDER_OR_UNSAT, 1),
];

#[test]
fn a_crossed_binder_universal_is_activated_by_discovery_not_by_its_static_registration() {
    for (name, text, level) in CROSSED_CASES {
        let (verdict, stats) = at_level(level, || ematch(text));
        assert!(
            matches!(verdict, CheckResult::Unsat),
            "{name} at level {level}: not refuted ({verdict:?}, {stats:?})"
        );
        assert!(
            stats.inert_crossed_binder >= 1,
            "{name} at level {level}: the static crossed-binder registration is \
             missing, so this fixture does not exercise the shape ({stats:?})"
        );
        assert!(
            stats.discovered >= 2,
            "{name} at level {level}: discovery did not register both the \
             middle universal (from the outer instance) and the inner one (from \
             the staged replacement) ({stats:?})"
        );
        assert!(
            stats.handed_off >= 1 && stats.staged_ground >= 1,
            "{name} at level {level}: nothing handed off or staged ({stats:?})"
        );
    }
}

/// The DROP half of the same shape, as its own test so a mutation of the drop
/// charging is attributable apart from one of the registration attribution:
/// the static crossed-binder registration matched, every one of its tuples was
/// dropped, and every drop is charged to the crossed-binder class.
#[test]
fn the_static_crossed_binder_registration_drops_in_the_crossed_binder_class() {
    for (name, text, level) in CROSSED_CASES {
        let (_, stats) = at_level(level, || ematch(text));
        assert!(
            stats.dropped > 0,
            "{name} at level {level}: the static registration never matched, so \
             the crossed-binder drop is not exercised ({stats:?})"
        );
        assert_eq!(
            stats.dropped_crossed_binder, stats.dropped,
            "{name} at level {level}: a drop on this shape that is NOT charged to \
             the crossed-binder class ({stats:?})"
        );
    }
}

/// With `=>` above the binder, level 0 refuses the connective FIRST, and the
/// attribution names the outermost obstacle: both static registrations are
/// `untracked`, none `crossed-binder`. First cause wins, because it is the
/// obstacle a remedy has to remove first.
#[test]
fn at_level_0_the_connective_above_the_binder_is_the_attributed_obstacle() {
    let (verdict, stats) = at_level(0, || ematch(CROSSED_BINDER_UNSAT));
    assert!(
        !matches!(verdict, CheckResult::Unsat),
        "level 0 refuted the `=>`-shaped crossed fixture through the isolated \
         loop ({verdict:?})"
    );
    assert_eq!(stats.registrations, 2, "{stats:?}");
    assert_eq!(stats.inert_untracked, 2, "{stats:?}");
    assert_eq!(stats.inert_crossed_binder, 0, "{stats:?}");
    assert_eq!(stats.dropped_untracked, stats.dropped, "{stats:?}");
}

/// The negative class: a universal under `not` is registered inert as
/// `negative` at level 1 (the flip is tracked) and as `untracked` at level 0
/// (the `not` step is refused), and its tuples are dropped in that class.
#[test]
fn a_negative_position_universal_is_dropped_in_the_negative_class() {
    let (verdict, stats) = at_level(1, || ematch(NEGATIVE_POSITION_SAT));
    assert!(
        !matches!(verdict, CheckResult::Unsat),
        "SAT fixture refuted"
    );
    assert_eq!(stats.inert_negative, 1, "{stats:?}");
    assert!(stats.joined > 0, "the negative registration never matched");
    assert_eq!(stats.dropped_negative, stats.dropped, "{stats:?}");
    assert_eq!(stats.dropped, stats.joined, "{stats:?}");

    let (_, shipped) = at_level(0, || ematch(NEGATIVE_POSITION_SAT));
    assert_eq!(shipped.inert_untracked, 1, "{shipped:?}");
    assert_eq!(shipped.inert_negative, 0, "{shipped:?}");
}

// ---------------------------------------------------------------------------
// Soundness-negative: the SAT twins, loop and front door, both levels.
// ---------------------------------------------------------------------------

#[test]
fn a_satisfiable_nested_shape_is_not_refuted_at_any_level() {
    for level in LEVELS {
        for (name, text) in SAT_FIXTURES {
            let (verdict, stats) = at_level(level, || ematch(text));
            assert!(
                !matches!(verdict, CheckResult::Unsat),
                "loop, {name} at level {level}: a SATISFIABLE query was refuted \
                 ({stats:?})"
            );
            let (verdict, _) = at_level(level, || front_door(text));
            assert!(
                !matches!(verdict, CheckResult::Unsat),
                "front door, {name} at level {level}: a SATISFIABLE query was refuted"
            );
        }
    }
}

/// The front door refutes every UNSAT fixture at BOTH levels — including the
/// brief's fixture at level 0, which the isolated loop cannot: the front
/// door's normalisation rewrites `=>` into `or`/`not`, and the path to the
/// inner universal is then the `or`-only shape level 0 already tracks. That
/// is a whitelist fact, and it is the reason the isolated loop is the
/// attributable instrument above.
#[test]
fn the_front_door_refutes_every_unsat_fixture_at_both_levels() {
    for level in LEVELS {
        for (name, text) in UNSAT_FIXTURES {
            let (verdict, stats) = at_level(level, || front_door(text));
            assert!(
                matches!(verdict, CheckResult::Unsat),
                "front door, {name} at level {level}: not refuted ({verdict:?}, {stats:?})"
            );
        }
    }
    // And the normalisation claim itself, as a counter: at level 0 the front
    // door's loop hands the brief's fixture off, where the isolated loop dropped it.
    let (_, stats) = at_level(0, || front_door(NESTED_UNDER_IMPLIES_UNSAT));
    assert!(
        stats.handed_off >= 1 && stats.dropped_untracked == 0,
        "the front door at level 0 did not reach the brief's fixture through \
         an `or`-only path ({stats:?})"
    );
}

// ---------------------------------------------------------------------------
// The instrument's own contracts.
// ---------------------------------------------------------------------------

/// The split partitions the drop count and the class partitions the
/// registration count, on every fixture at every level. A split that did not
/// sum would be reporting a fourth, unnamed class.
#[test]
fn the_drop_split_and_the_inert_split_partition_their_totals() {
    for level in LEVELS {
        for (name, text) in SAT_FIXTURES.iter().chain(UNSAT_FIXTURES.iter()) {
            let (_, s) = at_level(level, || ematch(text));
            assert_eq!(
                s.dropped,
                s.dropped_crossed_binder + s.dropped_negative + s.dropped_untracked,
                "{name} at level {level}: the drop split does not sum ({s:?})"
            );
            assert_eq!(
                s.registrations,
                s.with_context + s.inert_crossed_binder + s.inert_negative + s.inert_untracked,
                "{name} at level {level}: the inert split does not sum ({s:?})"
            );
            assert_eq!(
                s.joined,
                s.handed_off + s.positive_capped + s.dropped,
                "{name} at level {level}: joined tuples that went nowhere ({s:?})"
            );
        }
    }
}

/// The guard resets on `enable()` and is thread-local, like every other
/// opt-in diagnostic here; a reading that leaked across tests would make the
/// counts above sums over whatever ran before.
#[test]
fn the_stats_guard_resets_and_does_not_cross_a_thread_boundary() {
    let (_, first) = at_level(1, || ematch(CROSSED_BINDER_UNSAT));
    assert!(first.registrations > 0, "the fixture registers nothing");
    let (_, again) = at_level(1, || ematch(CROSSED_BINDER_UNSAT));
    assert_eq!(
        first, again,
        "a second enable() did not reset the accumulator"
    );
    let elsewhere = std::thread::spawn(last_nested_activation_stats)
        .join()
        .expect("worker finished");
    assert_eq!(
        elsewhere,
        NestedActivationStats::default(),
        "another thread read this thread's accumulator"
    );
}

// ---------------------------------------------------------------------------
// The certificate: a refutation through a discovered registration carries a
// replacement whose OWNER is itself derived, and every link checks.
// ---------------------------------------------------------------------------

#[test]
fn a_nested_refutation_carries_a_checked_replacement_chain() {
    let _level = PositivePathLevelGuard::set(1);
    let mut script = parse_script(CROSSED_BINDER_UNSAT).expect("parses");
    let mut certificate = None;
    let verdict = prove_quantified_unsat_via_egraph_with_instances(
        &mut script.arena,
        &script.assertions,
        &config(),
        &mut certificate,
    )
    .expect("no solver error");
    assert!(
        matches!(verdict, CheckResult::Unsat),
        "not refuted: {verdict:?}"
    );
    let derivations = certificate.expect(
        "the refutation carried NO derivations: `collect_ground_derivations` \
         declined, which is the uncertified path ADR-2120 closed",
    );
    let chained = derivations
        .iter()
        .filter(|derivation| {
            matches!(
                derivation,
                QuantifierGroundDerivation::PositiveReplacement(replacement)
                    if replacement.owner_derivation.is_some()
            )
        })
        .count();
    assert!(
        chained >= 1,
        "no replacement in the certificate has a DERIVED owner, so the \
         refutation did not pass through a discovered registration: {derivations:?}"
    );
    for derivation in &derivations {
        assert!(
            check_quantifier_ground_derivation(&mut script.arena, &script.assertions, derivation),
            "a derivation in the certificate does not check: {derivation:?}"
        );
    }
}

// ---------------------------------------------------------------------------
// The lever: `AXEYUM_QINST_NESTED_ACTIVATION` / `NestedActivationLevelGuard`.
//
// Level 0 is the shipped discovery. Level 1 stops spending discovery's
// budgets on DUPLICATES: an admitted instance is not scanned (its universals
// are the assertion's own, already registered by the static walk), a staged
// replacement is scanned only inside its replaced subtree, and a re-derived
// conclusion does not spend `MAX_POSITIVE_INSTANCES` again. Level 2 adds the
// reference solvers' ingestion rule: a quantifier inside a ground formula is
// ONE opaque leaf of the e-graph and its body is never walked, so a
// registration's trigger can no longer match its own body inside an admitted
// instance and hand off a tuple that binds a variable to itself.
//
// The fixture below is the failure all three levels are measured on: enough
// duplicate exposures to fill every discovery budget, then one crossed-binder
// refutation whose only route is a discovered registration.
// ---------------------------------------------------------------------------

const NESTED_LEVELS: [usize; 3] = [0, 1, 2];

/// `forall x. (¬P(x) ∨ forall y. Q(x,y))` with `P(a_1) … P(a_n)`, beside
/// `forall x. (¬S(x) ∨ forall u. (¬R(x,u) ∨ forall y. T(u,y)))`, `S(d)`,
/// `¬T(c,b)` and — for the UNSAT twin — `R(d,c)`.
///
/// The `n` instances of the first universal each carry a residual
/// `forall y. Q(a_i, y)` into the ground set. At level 0 every one of them is
/// scanned into a duplicate registration (256 cap), its body is ingested so
/// the static `forall x y. Q(x,y)` matches `Q(a_i, y)` and hands off a tuple
/// binding `y` to itself every round (refused by the checker), and the
/// replacements that do check are re-derived every round until the 4,096
/// positive-instance cap is spent — after which `stage` breaks before it
/// reaches the one tuple that matters, `T(c, b)` against the discovered
/// `forall y. T(c,y)`.
fn crossed_after_duplicates(n: usize, unsat: bool) -> String {
    let mut text = String::from(
        "(set-logic UF)\n(declare-sort U 0)\n\
         (declare-fun P (U) Bool)\n(declare-fun Q (U U) Bool)\n\
         (declare-fun S (U) Bool)\n(declare-fun R (U U) Bool)\n(declare-fun T (U U) Bool)\n\
         (declare-const b U)\n(declare-const c U)\n(declare-const d U)\n\
         (assert (forall ((x U)) (or (not (P x)) (forall ((y U)) (Q x y)))))\n\
         (assert (forall ((x U)) (or (not (S x)) (forall ((u U)) (or (not (R x u)) (forall ((y U)) (T u y)))))))\n\
         (assert (S d))\n(assert (not (T c b)))\n",
    );
    text.push_str(if unsat {
        "(assert (R d c))\n"
    } else {
        "(assert (not (R d c)))\n"
    });
    for i in 0..n {
        text.push_str(&format!("(declare-const a{i} U)\n(assert (P a{i}))\n"));
    }
    text.push_str("(check-sat)\n");
    text
}

/// Enough duplicates to exceed `MAX_DISCOVERED_REGISTRATIONS` (256) in one
/// round with margin.
const DUPLICATES: usize = 300;

fn at_nested_level<T>(level: usize, run: impl FnOnce() -> T) -> T {
    let _guard = NestedActivationLevelGuard::set(level);
    run()
}

/// The shipped level fails the cap fixture, and the counters say on what: the
/// registration cap, the positive-instance cap, and the self-binding handoffs
/// the checker refuses — all three at once.
#[test]
fn the_shipped_level_spends_every_discovery_budget_on_duplicates() {
    let text = crossed_after_duplicates(DUPLICATES, true);
    let (verdict, stats) = at_level(0, || at_nested_level(0, || ematch(&text)));
    assert!(
        !matches!(verdict, CheckResult::Unsat),
        "the shipped level refuted the cap fixture, so it does not exercise the \
         caps and the conversions below prove nothing ({stats:?})"
    );
    assert!(
        stats.discovered >= 256,
        "MAX_DISCOVERED_REGISTRATIONS was not hit ({stats:?})"
    );
    assert!(
        stats.positive_instances >= 4096,
        "MAX_POSITIVE_INSTANCES was not hit ({stats:?})"
    );
    assert!(
        stats.rejected_by_checker > 0,
        "no self-binding tuple was handed off and refused ({stats:?})"
    );
    assert!(
        stats.dropped_crossed_binder > 0,
        "the static crossed-binder registration never matched ({stats:?})"
    );
}

/// THE conversion: level 2 refutes the cap fixture, through a discovered
/// registration, with no budget touched and no tuple refused.
#[test]
fn level_2_reaches_the_crossed_universal_the_shipped_budgets_refuse() {
    let text = crossed_after_duplicates(DUPLICATES, true);
    let (verdict, stats) = at_level(0, || at_nested_level(2, || ematch(&text)));
    assert!(
        matches!(verdict, CheckResult::Unsat),
        "level 2 did not refute the cap fixture ({verdict:?}, {stats:?})"
    );
    assert!(
        stats.discovered >= 1,
        "no discovered registration ({stats:?})"
    );
    assert!(
        stats.discovered < 256 && stats.positive_instances < 4096,
        "level 2 hit a cap too, so the conversion is not attributable to the \
         duplicates it stops spending on ({stats:?})"
    );
    assert_eq!(
        stats.rejected_by_checker, 0,
        "level 2 still handed off a tuple that binds a variable to itself, so \
         the opaque-binder ingestion did not take ({stats:?})"
    );
    assert!(
        stats.handed_off >= 1 && stats.staged_ground >= 1,
        "the refutation did not pass through a staged replacement ({stats:?})"
    );
}

/// Level 1's two halves, each read from its own counter on the cap fixture:
/// the instances are not scanned, and a re-derived conclusion no longer spends
/// the positive-instance cap. Level 1 alone does NOT convert the fixture —
/// the self-binding handoffs still flood the per-round cap — which is why
/// level 2 exists and is stated here rather than left to be inferred.
#[test]
fn level_1_stops_spending_the_budgets_on_duplicates_but_the_flood_remains() {
    let text = crossed_after_duplicates(DUPLICATES, true);
    let (_, stats) = at_level(0, || at_nested_level(1, || ematch(&text)));
    assert!(
        stats.instances_unscanned >= DUPLICATES,
        "level 1 scanned the admitted instances ({stats:?})"
    );
    assert!(
        stats.discovered < 256,
        "level 1 hit MAX_DISCOVERED_REGISTRATIONS ({stats:?})"
    );
    assert!(
        stats.positive_instances < 4096,
        "level 1 spent MAX_POSITIVE_INSTANCES on re-derived conclusions ({stats:?})"
    );
    assert!(
        stats.rejected_by_checker > 0,
        "level 1 handed off no self-binding tuple; then the flood level 2 \
         removes is not exercised here ({stats:?})"
    );
}

/// The SAT twin of the cap fixture at every level of both levers. Level 2 is
/// the arm that reaches the crossed universal, so it is the arm where a
/// replacement admitted without its activation literal would show.
#[test]
fn the_cap_fixtures_satisfiable_twin_is_not_refuted_at_any_level_of_either_lever() {
    let text = crossed_after_duplicates(DUPLICATES, false);
    for positive in LEVELS {
        for nested in NESTED_LEVELS {
            let (verdict, stats) = at_level(positive, || at_nested_level(nested, || ematch(&text)));
            assert!(
                !matches!(verdict, CheckResult::Unsat),
                "positive-path {positive}, nested-activation {nested}: a \
                 SATISFIABLE query was refuted ({stats:?})"
            );
        }
    }
}

/// Every satisfiable fixture in this file, at every level of BOTH levers,
/// through the loop and the front door.
#[test]
fn a_satisfiable_nested_shape_is_not_refuted_at_any_nested_activation_level() {
    for positive in LEVELS {
        for nested in NESTED_LEVELS {
            for (name, text) in SAT_FIXTURES {
                let (verdict, stats) =
                    at_level(positive, || at_nested_level(nested, || ematch(text)));
                assert!(
                    !matches!(verdict, CheckResult::Unsat),
                    "loop, {name} at positive-path {positive} / nested-activation \
                     {nested}: a SATISFIABLE query was refuted ({stats:?})"
                );
                let (verdict, _) =
                    at_level(positive, || at_nested_level(nested, || front_door(text)));
                assert!(
                    !matches!(verdict, CheckResult::Unsat),
                    "front door, {name} at positive-path {positive} / \
                     nested-activation {nested}: a SATISFIABLE query was refuted"
                );
            }
        }
    }
}

/// Level 1 registers a strict SUBSET of level 0's registrations: on the
/// crossed shape it skips the outer instance's exposure of the middle
/// universal (a duplicate of the static registration) and keeps the one
/// crossed universal. This is the test a mutation that makes level 1 behave
/// like level 0 has to fail.
#[test]
fn level_1_registers_a_strict_subset_and_counts_what_it_skipped() {
    let (_, shipped) = at_level(0, || at_nested_level(0, || ematch(CROSSED_BINDER_OR_UNSAT)));
    let (verdict, raised) = at_level(0, || at_nested_level(1, || ematch(CROSSED_BINDER_OR_UNSAT)));
    assert!(
        matches!(verdict, CheckResult::Unsat),
        "level 1 lost the refutation"
    );
    assert_eq!(
        shipped.instances_unscanned + shipped.discovered_outside_scope,
        0,
        "level 0 skipped something; it has no scope rule ({shipped:?})"
    );
    assert!(
        raised.discovered < shipped.discovered,
        "level 1 did not register strictly fewer than level 0 ({raised:?} vs {shipped:?})"
    );
    assert!(
        raised.discovered >= 1,
        "level 1 registered nothing, so the refutation did not come through a \
         discovered registration ({raised:?})"
    );
    assert!(
        raised.instances_unscanned >= 1,
        "level 1 registered fewer but scanned every instance, so the difference \
         is not the rule under test ({raised:?})"
    );
}

/// Level 2's ingestion rule, read on the crossed shape: the same refutation,
/// and not one self-binding tuple handed off, where levels 0 and 1 hand off
/// several and have them refused.
#[test]
fn level_2_hands_off_no_tuple_that_binds_a_variable_to_itself() {
    let (_, shipped) = at_level(0, || at_nested_level(0, || ematch(CROSSED_BINDER_OR_UNSAT)));
    assert!(
        shipped.rejected_by_checker > 0,
        "the shipped level refused nothing on this shape, so the rule has \
         nothing to remove here ({shipped:?})"
    );
    let (verdict, opaque) = at_level(0, || at_nested_level(2, || ematch(CROSSED_BINDER_OR_UNSAT)));
    assert!(
        matches!(verdict, CheckResult::Unsat),
        "level 2 lost the refutation"
    );
    assert_eq!(opaque.rejected_by_checker, 0, "{opaque:?}");
    assert!(
        opaque.joined < shipped.joined,
        "level 2 joined no fewer tuples than level 0 ({opaque:?} vs {shipped:?})"
    );
}

/// What level 0 refutes, levels 1 and 2 refute: the lever removes duplicates
/// and non-ground matches, never a route. Every UNSAT fixture in this file,
/// at both positive-path levels.
#[test]
fn a_refutation_the_shipped_nested_level_finds_survives_the_raised_levels() {
    for positive in LEVELS {
        for (name, text) in UNSAT_FIXTURES {
            let shipped = at_level(positive, || at_nested_level(0, || ematch(text))).0;
            if !matches!(shipped, CheckResult::Unsat) {
                continue;
            }
            for nested in [1, 2] {
                let raised = at_level(positive, || at_nested_level(nested, || ematch(text))).0;
                assert!(
                    matches!(raised, CheckResult::Unsat),
                    "{name} at positive-path {positive}: nested-activation 0 refutes \
                     and {nested} does not"
                );
            }
        }
    }
}

/// The cap fixture's refutation at level 2 carries the same certificate chain
/// as every other nested refutation: a replacement whose owner is itself
/// derived, every link checked. The lever changes what is REGISTERED and
/// INGESTED, not what is trusted.
#[test]
fn the_level_2_refutation_carries_a_checked_replacement_chain() {
    let _positive = PositivePathLevelGuard::set(0);
    let _nested = NestedActivationLevelGuard::set(2);
    let text = crossed_after_duplicates(DUPLICATES, true);
    let mut script = parse_script(&text).expect("parses");
    let mut certificate = None;
    let verdict = prove_quantified_unsat_via_egraph_with_instances(
        &mut script.arena,
        &script.assertions,
        &config(),
        &mut certificate,
    )
    .expect("no solver error");
    assert!(
        matches!(verdict, CheckResult::Unsat),
        "not refuted: {verdict:?}"
    );
    let derivations = certificate.expect("the level-2 refutation carried no derivations");
    assert!(
        derivations.iter().any(|derivation| matches!(
            derivation,
            QuantifierGroundDerivation::PositiveReplacement(replacement)
                if replacement.owner_derivation.is_some()
        )),
        "no replacement with a derived owner: {derivations:?}"
    );
    for derivation in &derivations {
        assert!(
            check_quantifier_ground_derivation(&mut script.arena, &script.assertions, derivation),
            "a derivation does not check: {derivation:?}"
        );
    }
}

#[test]
fn the_nested_activation_guard_restores_and_does_not_cross_a_thread_boundary() {
    let text = crossed_after_duplicates(DUPLICATES, true);
    let outer = NestedActivationLevelGuard::set(2);
    let inside_worker = std::thread::spawn({
        let text = text.clone();
        move || at_level(0, || ematch(&text)).1.discovered
    })
    .join()
    .expect("worker finished");
    drop(outer);
    let shipped = at_level(0, || ematch(&text)).1.discovered;
    assert_eq!(
        inside_worker, shipped,
        "the worker thread saw a level the guard set on another thread"
    );
    {
        let _raised = NestedActivationLevelGuard::set(2);
        assert!(
            at_level(0, || ematch(&text)).1.discovered < shipped,
            "the guard did not take effect on its own thread"
        );
    }
    assert_eq!(
        at_level(0, || ematch(&text)).1.discovered,
        shipped,
        "the guard leaked past its own lifetime"
    );
}
