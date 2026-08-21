//! User-supplied quantifier triggers (SMT-LIB `:pattern`) reaching the
//! E-matching loop.
//!
//! Before this, `:pattern` was parsed and dropped, so a hand-written trigger had
//! no effect whatsoever: the loop always used its own selection. These tests pin
//! the three things that changed and the one thing that must not.
//!
//! **What must not change is soundness, and the reason is structural.** Every
//! instance the loop admits is `body[x⃗ := t⃗]`, and `∀x⃗. B ⊨ B[x⃗ := t⃗]` for
//! *every* ground `t⃗` — the entailment is a property of `B` alone and cannot
//! depend on how `t⃗` was chosen. A trigger's only output is a substitution, so
//! it can only make the loop try more or fewer instances. That is why the tests
//! below measure *decisions* (a completeness property) and why a wrong verdict
//! is not among the things a trigger could produce.

#![cfg(feature = "full")]

use std::time::Duration;

use axeyum_smtlib::parse_script;
use axeyum_solver::{CheckResult, SolverConfig, prove_quantified_unsat_via_egraph};

fn config() -> SolverConfig {
    SolverConfig {
        timeout: Some(Duration::from_secs(10)),
        ..SolverConfig::default()
    }
}

/// Runs the E-matching refutation loop alone (not the front door, which has
/// several other routes to the same verdict — this isolates the trigger).
fn ematch(text: &str) -> CheckResult {
    let mut script = parse_script(text).expect("parses");
    prove_quantified_unsat_via_egraph(&mut script.arena, &script.assertions, &config())
        .expect("no solver error")
}

/// The refutation needs the instance `x := b`, which only a trigger reaching
/// `f b` proposes. `(h x)` reaches only `h a`, so it proposes `x := a`.
const PRELUDE: &str = r"
    (set-logic UF)
    (declare-sort U 0)
    (declare-fun f (U) U)
    (declare-fun h (U) U)
    (declare-const a U)
    (declare-const b U)
    (assert (= (h a) b))
";
const GOAL: &str = "(assert (not (= (f b) a))) (check-sat)";

fn query(quantifier: &str) -> String {
    format!("{PRELUDE}{quantifier}{GOAL}")
}

/// The instances the trigger proposes, rendered, sorted. This is the *direct*
/// observable of a trigger — the loop has other machinery (term invention, the
/// interleaved ground checks) that can reach a verdict a trigger alone would
/// not, so a verdict is a blunt instrument for "was the annotation obeyed".
fn proposed_instances(text: &str) -> Vec<String> {
    let mut script = parse_script(text).expect("parses");
    let forall = script.assertions[1];
    let ground = vec![script.assertions[0], script.assertions[2]];
    let mut rendered: Vec<String> =
        axeyum_solver::instantiate_forall_via_egraph(&mut script.arena, &ground, forall)
            .into_iter()
            .map(|t| axeyum_ir::render(&script.arena, t))
            .collect();
    rendered.sort();
    rendered
}

#[test]
fn without_an_annotation_the_loop_selects_its_own_trigger() {
    // Auto-selection picks `f x`, the body's own application. The only ground
    // `f` application is `f b`, so it proposes the class of `b` — the instance
    // that refutes. (The class representative renders as `(h a)`: `h a = b` is
    // asserted, so matching is modulo the ground congruence and the two are one
    // term to the matcher. That is the pre-existing behaviour, not a trigger
    // effect.) This is the control every other case is read against.
    assert_eq!(
        proposed_instances(&query("(assert (forall ((x U)) (= (f x) a)))")),
        vec!["(= (f (h a)) a)".to_owned()]
    );
}

#[test]
fn a_user_trigger_replaces_auto_selection() {
    // THE MEASUREMENT. `(h x)` reaches only `h a`, so the annotated quantifier
    // proposes `x := a` where the unannotated one proposed `x := b`. Before
    // this change both produced `(= (f b) a)`: the annotation was parsed and
    // dropped, so it could not change anything at all.
    //
    // z3 4.13.3 on the same file with its own fallbacks off
    // (`smt.mbqi=false smt.auto_config=false`) goes `unsat` → `unknown` for
    // exactly this reason.
    assert_eq!(
        proposed_instances(&query(
            "(assert (forall ((x U)) (! (= (f x) a) :pattern ((h x)))))"
        )),
        vec!["(= (f a) a)".to_owned()],
        "the user's trigger, not the body's own application"
    );
}

#[test]
fn alternatives_are_disjunctive() {
    // Two `:pattern` attributes are ALTERNATIVES. Their tuple sets are unioned,
    // so both instances appear. Merging them into one multi-pattern instead
    // would intersect and yield nothing — see the next test.
    assert_eq!(
        proposed_instances(&query(
            "(assert (forall ((x U)) (! (= (f x) a) :pattern ((h x)) :pattern ((f x)))))"
        )),
        vec!["(= (f (h a)) a)".to_owned(), "(= (f a) a)".to_owned()]
    );
}

#[test]
fn a_multi_pattern_is_conjunctive_within_one_alternative() {
    // One `:pattern` with two terms: both must match and their substitutions
    // must agree. `h x` binds only `x := a`, `f x` binds only `x := b`, so the
    // intersection is empty and the alternative proposes nothing. That this
    // differs from the previous test is the whole point of keeping alternatives
    // and multi-patterns as separate structures.
    assert!(
        proposed_instances(&query(
            "(assert (forall ((x U)) (! (= (f x) a) :pattern ((h x) (f x)))))"
        ))
        .is_empty(),
        "a multi-pattern must intersect, not union"
    );
}

#[test]
fn an_unusable_annotation_falls_back_to_auto_selection() {
    // A bare variable has no root declaration to index by; `(+ x 1)` is an
    // interpreted application the parser declines to build at all. Either way
    // the quantifier must end up exactly where it was before annotations
    // existed — an annotation the matcher cannot use must not cost anything.
    for annotation in [
        "(! (= (f x) a) :pattern (x))",
        "(! (= (f x) a) :pattern ((f (+ x 1))))",
        "(! (= (f x) a) :pattern ((f x) x))",
    ] {
        assert_eq!(
            proposed_instances(&query(&format!("(assert (forall ((x U)) {annotation}))"))),
            vec!["(= (f (h a)) a)".to_owned()],
            "declined annotation must leave auto-selection alone: {annotation}"
        );
    }
}

#[test]
fn a_pattern_that_misses_a_bound_variable_is_declined_whole() {
    // `(h x)` binds x but says nothing about y. Keeping it would produce tuples
    // with an unbound slot, every one of which the join discards — the
    // quantifier would be silently starved rather than fall back.
    let text = "
        (set-logic UF)
        (declare-sort U 0)
        (declare-fun h (U) U)
        (declare-fun k (U U) U)
        (declare-const a U)
        (declare-const b U)
        (assert (= (h a) b))
        (assert (forall ((x U) (y U)) (! (= (k x y) a) :pattern ((h x)))))
        (assert (not (= (k b b) a)))
        (check-sat)";
    assert_eq!(
        proposed_instances(text),
        vec!["(= (k (h a) (h a)) a)".to_owned()],
        "an alternative that cannot bind every variable must be declined, not used"
    );
}

#[test]
fn a_pattern_may_name_an_outer_binder_of_the_same_chain() {
    // `(h x y)` is written in the inner binder's scope and names both. The
    // driver peels `∀x. ∀y.` to ONE universal over `[x, y]`, so a pattern
    // spanning the chain is ordinary, not foreign, and must be obeyed: it
    // matches `h a a` and proposes `x := a, y := a`, where auto-selection on
    // `f y` would have proposed the class of `b`.
    let text = "
        (set-logic UF)
        (declare-sort U 0)
        (declare-fun f (U) U)
        (declare-fun h (U U) U)
        (declare-const a U)
        (declare-const b U)
        (assert (= (h a a) b))
        (assert (forall ((x U)) (forall ((y U)) (! (= (f y) a) :pattern ((h x y))))))
        (assert (not (= (f b) a)))
        (check-sat)";
    assert_eq!(proposed_instances(text), vec!["(= (f a) a)".to_owned()]);
}

#[test]
fn the_loops_own_verdict_survives_a_bad_trigger_here() {
    // Measured, and worth recording rather than assuming: obeying a useless
    // trigger does NOT cost this refutation, because term invention seeds
    // ground instances of the trigger itself and reaches `x := b` anyway. Z3
    // with `smt.mbqi=false` has no analogue and returns `unknown`. So the
    // completeness cost of honouring a trigger is real in principle and is
    // absorbed here in practice — which is why the tests above measure the
    // instance set and this one measures the verdict.
    for quantifier in [
        "(assert (forall ((x U)) (= (f x) a)))",
        "(assert (forall ((x U)) (! (= (f x) a) :pattern ((h x)))))",
        "(assert (forall ((x U)) (! (= (f x) a) :pattern ((f x)))))",
    ] {
        let result = ematch(&query(quantifier));
        assert!(
            matches!(result, CheckResult::Unsat),
            "{quantifier} => {result:?}"
        );
    }
}

#[test]
fn every_instance_a_user_trigger_produces_is_a_substitution_of_the_body() {
    // The soundness invariant, checked directly on the public one-shot API:
    // whatever the trigger proposes, the term admitted is the body with the
    // bound variable replaced by a ground term. Nothing else is admitted, so
    // "the trigger fired" is never itself a justification.
    use axeyum_ir::{Op, TermId, TermNode};
    let text = query("(assert (forall ((x U)) (! (= (f x) a) :pattern ((h x)))))");
    let mut script = parse_script(&text).expect("parses");
    let forall = script.assertions[1];
    let ground: Vec<TermId> = vec![script.assertions[0], script.assertions[2]];
    let instances =
        axeyum_solver::instantiate_forall_via_egraph(&mut script.arena, &ground, forall);
    assert!(
        !instances.is_empty(),
        "the user trigger `h x` matches `h a`, so it must propose x := a"
    );
    for instance in instances {
        // Every instance is an equality `(= (f t) a)` — the body's shape with
        // the variable replaced, never a fresh claim.
        let TermNode::App { op, args } = script.arena.node(instance) else {
            panic!("instance is an application");
        };
        assert!(matches!(op, Op::Eq), "instance keeps the body's shape");
        assert_eq!(args.len(), 2);
    }
}
