//! ADR-2000: the VERDICT half of the linear `distinct` encoding's obligation.
//!
//! `axeyum-smtlib/tests/distinct_linear_scope.rs` pins where the rewrite fires.
//! This pins what the solver then ANSWERS, because the shipped front door's
//! model replay cannot catch a weakened encoding:
//! `SmtLibSolved`'s replay is `check_model(&solved.script.arena,
//! &solved.assertions, model)` (`crates/axeyum-solver/src/smtlib.rs:4426`), and
//! `solved.assertions` are the assertions the PARSER produced — under this
//! rewrite, the rewritten ones. A model of the encoding replayed against the
//! encoding proves nothing about `distinct`. The `sat` direction is safe
//! because the encoding is at least as STRONG as `distinct` (any model of
//! `⋀ᵢ f(tᵢ) = i` makes the `tᵢ` pairwise distinct, since `f` is a function),
//! not because anything downstream checks it. That is exactly why the verdicts
//! below are asserted here.
//!
//! Every mutant arm in this file MUST flip a verdict. ADR-1976 measured that a
//! satisfiable query is a vacuous control — an underconstrained `sat` stays
//! `sat` under a broken rewrite — so each control is aimed at the direction
//! where the mutant has somewhere to go: the WEAKENING mutant at an `unsat`,
//! the STRENGTHENING mutant at a `sat`.

use axeyum_smtlib::parse_script_with_distinct_lever;
use axeyum_solver::{CheckResult, SolverConfig, check_auto};

/// Parse with an explicit lever and decide, flattening the scoped view.
fn verdict(src: &str, lever: Option<&str>) -> CheckResult {
    let mut script = parse_script_with_distinct_lever(src, lever)
        .unwrap_or_else(|e| panic!("parse failed for lever {lever:?}: {e:?}"));
    let assertions = script.assertions.clone();
    check_auto(&mut script.arena, &assertions, &SolverConfig::default())
        .unwrap_or_else(|e| panic!("solve failed for lever {lever:?}: {e:?}"))
}

fn is_sat(r: &CheckResult) -> bool {
    matches!(r, CheckResult::Sat(_))
}

fn name(r: &CheckResult) -> &'static str {
    match r {
        CheckResult::Sat(_) => "sat",
        CheckResult::Unsat => "unsat",
        CheckResult::Unknown(_) => "unknown",
    }
}

const PREAMBLE: &str = "(set-logic UFNIA)\n(declare-sort U 0)\n\
     (declare-fun a () U)\n(declare-fun b () U)\n(declare-fun c () U)\n";

/// `(distinct a b c)` alone: satisfiable.
const SAT_QUERY: &str = "(set-logic UFNIA)\n(declare-sort U 0)\n\
     (declare-fun a () U)\n(declare-fun b () U)\n(declare-fun c () U)\n\
     (assert (distinct a b c))\n(check-sat)\n";

/// The `unsat` twin, differing in ONE small term: `(= a b)`. A solver that
/// answered `unknown` to both could not pass the pair.
const UNSAT_QUERY: &str = "(set-logic UFNIA)\n(declare-sort U 0)\n\
     (declare-fun a () U)\n(declare-fun b () U)\n(declare-fun c () U)\n\
     (assert (distinct a b c))\n(assert (= a b))\n(check-sat)\n";

// ---------------------------------------------------------------------------
// The pair, under both arms
// ---------------------------------------------------------------------------

#[test]
fn the_sat_unsat_pair_is_decided_the_same_way_by_both_encodings() {
    let base_sat = verdict(SAT_QUERY, None);
    let base_unsat = verdict(UNSAT_QUERY, None);
    assert!(
        is_sat(&base_sat),
        "baseline: the pairwise path must decide the sat half; got {}",
        name(&base_sat)
    );
    assert_eq!(
        base_unsat,
        CheckResult::Unsat,
        "baseline: the pairwise path must decide the unsat half; got {}",
        name(&base_unsat)
    );

    let arm_sat = verdict(SAT_QUERY, Some("on:3"));
    let arm_unsat = verdict(UNSAT_QUERY, Some("on:3"));
    assert!(
        is_sat(&arm_sat),
        "the linear encoding turned a `sat` into {} -- it is STRONGER than `distinct`",
        name(&arm_sat)
    );
    assert_eq!(
        arm_unsat,
        CheckResult::Unsat,
        "the linear encoding turned an `unsat` into {} -- it is WEAKER than `distinct`",
        name(&arm_unsat)
    );
}

// ---------------------------------------------------------------------------
// The WEAKENING mutant, aimed at the `unsat`
// ---------------------------------------------------------------------------

#[test]
fn the_vacuous_mutant_breaks_the_unsat_and_that_is_what_makes_this_a_control() {
    // Every argument mapped to index 0: the conjunction constrains nothing, so
    // `(distinct a b c)` has been thrown away and `(= a b)` alone is
    // satisfiable. If this did NOT flip, the test above would be measuring the
    // rest of the query rather than the encoding.
    let mutated = verdict(UNSAT_QUERY, Some("mutant:vacuous:3"));
    assert!(
        !matches!(mutated, CheckResult::Unsat),
        "the vacuous mutant left the `unsat` in place -- the control is vacuous \
         and the zero above means nothing"
    );
    assert!(
        is_sat(&mutated),
        "the vacuous mutant must make this query `sat`, not {}",
        name(&mutated)
    );
}

// ---------------------------------------------------------------------------
// The STRENGTHENING mutant, aimed at the `sat`
// ---------------------------------------------------------------------------

/// Two applications sharing an argument at different indices. Satisfiable: four
/// pairwise-distinct constants exist in an uninterpreted sort.
const TWO_APPLICATIONS_SAT: &str = "(set-logic UFNIA)\n(declare-sort U 0)\n\
     (declare-fun a () U)\n(declare-fun b () U)\n(declare-fun c () U)\n\
     (declare-fun d () U)\n\
     (assert (distinct a b c))\n(assert (distinct c a d))\n(check-sat)\n";

#[test]
fn the_shared_injection_mutant_breaks_the_sat() {
    let honest = verdict(TWO_APPLICATIONS_SAT, Some("on:3"));
    assert!(
        is_sat(&honest),
        "two `distinct` applications over four constants are satisfiable; \
         a fresh injection each must keep it `sat`, got {}",
        name(&honest)
    );
    // One shared `f` forces `f(a) = 0` from the first application and
    // `f(a) = 1` from the second: a spurious `unsat`. This is the exact defect
    // the fresh-name probe exists to prevent, and it must be reachable, or the
    // probe is guarding nothing.
    let mutated = verdict(TWO_APPLICATIONS_SAT, Some("mutant:shared:3"));
    assert_eq!(
        mutated,
        CheckResult::Unsat,
        "the shared-injection mutant must manufacture an `unsat` here; got {} -- \
         if it cannot, the freshness guard is untested",
        name(&mutated)
    );
}

// ---------------------------------------------------------------------------
// Polarity: the hazard is real, and the guard is what keeps it out
// ---------------------------------------------------------------------------

/// `(not (distinct a b c))` together with all three pairwise disequalities:
/// UNSAT, because the negation says two of the three coincide.
const NEGATED_QUERY: &str = "(set-logic UFNIA)\n(declare-sort U 0)\n\
     (declare-fun a () U)\n(declare-fun b () U)\n(declare-fun c () U)\n\
     (assert (not (distinct a b c)))\n\
     (assert (not (= a b)))\n(assert (not (= a c)))\n(assert (not (= b c)))\n\
     (check-sat)\n";

/// The SAME query with the `distinct` under the negation replaced by the
/// injection encoding BY HAND — i.e. what a parser without the polarity guard
/// would build. `f` is a user symbol here, but that is the point: the encoding
/// under a negation is satisfiable by any `f` that disagrees with the indexing,
/// whatever `a`, `b`, `c` are.
const NEGATED_QUERY_REWRITTEN_UNDER_THE_NEGATION: &str = "(set-logic UFNIA)\n\
     (declare-sort U 0)\n\
     (declare-fun a () U)\n(declare-fun b () U)\n(declare-fun c () U)\n\
     (declare-fun f (U) Int)\n\
     (assert (not (and (= (f a) 0) (= (f b) 1) (= (f c) 2))))\n\
     (assert (not (= a b)))\n(assert (not (= a c)))\n(assert (not (= b c)))\n\
     (check-sat)\n";

#[test]
fn rewriting_under_a_negation_would_be_a_wrong_sat() {
    // The hazard, demonstrated rather than asserted. This is the non-vacuity
    // evidence for the guard: without it, the two verdicts below would be the
    // SAME parse of the same source file.
    let honest = verdict(NEGATED_QUERY, None);
    assert_eq!(
        honest,
        CheckResult::Unsat,
        "`(not (distinct a b c))` with all three pairwise disequalities is unsat; got {}",
        name(&honest)
    );
    let hazard = verdict(NEGATED_QUERY_REWRITTEN_UNDER_THE_NEGATION, None);
    assert!(
        is_sat(&hazard),
        "the polarity hazard must be REAL: the encoding placed under the negation \
         has to be satisfiable, or this guard protects against nothing; got {}",
        name(&hazard)
    );
}

#[test]
fn the_guard_keeps_the_negated_query_unsat_under_the_lever() {
    for lever in [None, Some("on:3"), Some("on:2")] {
        let r = verdict(NEGATED_QUERY, lever);
        assert_eq!(
            r,
            CheckResult::Unsat,
            "lever {lever:?} changed a negated `distinct` query's verdict to {} -- \
             the polarity guard leaked",
            name(&r)
        );
    }
}

// ---------------------------------------------------------------------------
// Freshness against a colliding user name
// ---------------------------------------------------------------------------

#[test]
fn a_user_symbol_spelled_like_the_injection_cannot_make_a_sat_query_unsat() {
    // `|!distinct.inj.0|` is a legal SMT-LIB symbol and this benchmark pins one
    // of its values. If the rewrite reused it, `(= (f a) 7)` and `(= (f a) 0)`
    // would contradict and this satisfiable query would come back `unsat`.
    let src = format!(
        "{PREAMBLE}(declare-fun |!distinct.inj.0| (U) Int)\n\
         (assert (= (|!distinct.inj.0| a) 7))\n\
         (assert (distinct a b c))\n(check-sat)\n"
    );
    for lever in [None, Some("on:3")] {
        let r = verdict(&src, lever);
        assert!(
            is_sat(&r),
            "lever {lever:?}: a user symbol spelled like the injection made a \
             satisfiable query {}",
            name(&r)
        );
    }
}

// ---------------------------------------------------------------------------
// The scale the encoding exists for
// ---------------------------------------------------------------------------

#[test]
fn an_arity_over_the_pairwise_cap_is_refused_without_the_lever_and_cleared_with_it() {
    // 400 nullary constants of an uninterpreted sort: `400 * 399 / 2 = 79,800`
    // pairs, over `MAX_DISTINCT_EXPANSION_PAIRS`. This is the shape of all 356
    // corpus files and the reason the encoding exists.
    //
    // The SAT direction at this scale is NOT asserted here. It is not cheap --
    // a model over 400 elements of an uninterpreted sort took over 11 minutes of
    // CPU in a debug build, which is a gate nobody would run -- and it is the
    // A/B's job, not a unit test's. What is asserted is the two things a unit
    // test can settle in milliseconds: the cap is real without the lever, the
    // encoding is built with it, and the UNSAT twin is still refuted.
    let names: Vec<String> = (0..400).map(|i| format!("k{i}")).collect();
    let mut decls = String::from("(set-logic UFNIA)\n(declare-sort U 0)\n");
    for n in &names {
        decls.push_str(&format!("(declare-fun {n} () U)\n"));
    }
    let big = format!("(distinct {})", names.join(" "));
    let src = format!("{decls}(assert {big})\n(check-sat)\n");

    assert!(
        parse_script_with_distinct_lever(&src, None).is_err(),
        "without the lever this must still hit the deterministic pairwise cap"
    );
    let script = parse_script_with_distinct_lever(&src, Some("on"))
        .expect("the lever must clear the front door at this arity");
    assert!(
        script
            .arena
            .find_internal_function("!distinct.inj.0")
            .is_some(),
        "the bare `on` lever must fire at arity 400"
    );

    // The unsat twin, differing in ONE small term. Under the encoding
    // `f(k0) = 0`, `f(k1) = 1` and `k0 = k1` contradict by congruence, so this
    // is refuted without ever building a 400-element model.
    let twin = format!("{decls}(assert {big})\n(assert (= k0 k1))\n(check-sat)\n");
    assert!(
        parse_script_with_distinct_lever(&twin, None).is_err(),
        "the twin must be refused by the cap too, or the pair is not a pair"
    );
    let r = verdict(&twin, Some("on"));
    assert_eq!(
        r,
        CheckResult::Unsat,
        "an over-cap `distinct` with two of its arguments equated is unsat; got {}",
        name(&r)
    );
}
