//! A **ground** dispatch rung's fragment refusal must not become the query's
//! verdict (ADR-1966).
//!
//! # Why this suite exists next to `quant_ladder_rung_refusal_declines`
//!
//! ADR-1927 established the rule for the rungs of the QUANTIFIED ladder in
//! [`axeyum_solver::solve`], and its own closing line says the audit was not
//! exhaustive. It was not: the same shape sits in `check_auto_dispatch`, the
//! quantifier-free theory ladder every query passes through, where a rung's
//! `Err(SolverError::Unsupported)` was propagated with a bare `?` and ended
//! the dispatch. The front door then printed `give-up kind=Error`, which is
//! not a verdict at all — "`unknown` is a first-class solver result, never an
//! error" (`CLAUDE.md`, Hard Rules).
//!
//! The population behind this suite was enumerated mechanically by
//! `scripts/enumerate-dispatch-refusal-propagation.py`, not by reading, and is
//! pinned with a `--fail-on-new` ratchet.
//!
//! # The fixture is DISCRIMINATING, and that was not free
//!
//! The obvious fixture — the refusing shape plus a ground contradiction
//! `x > 0 AND x < 0` — is **vacuous here**, and was written and thrown away
//! before this file reached its present form. `int-box-eval` refutes such a
//! query at `attempts=3`, long before the ladder reaches the rung under test,
//! so both arms answer `unsat` and the test passes on the unfixed tree. The
//! fixture below was instead checked against a binary built WITHOUT the guards
//! and kept only because the two arms differ:
//!
//! | fixture | without the guards | with them |
//! |---|---|---|
//! | [`ARRAY_VALUED_UF_SAT`] | `Err`, `attempts=17` | `Ok(Unknown)`, `attempts=20` |
//!
//! # The datatype rung, taken by ADR-1980
//!
//! `check_auto_dispatch`'s `check_with_datatype_native` site is the same shape
//! and was worth **+22 `AUFDTLIRA` files, every one confirmed `unsat` by z3
//! 4.13.3 and cvc5 1.3.4** (`bench-results/dispatch-decline-audit-20260913/`).
//! ADR-1966 measured it and left it, because converting it turned 7 assertions
//! red in four registered suites owned by ADR-1920/1935/1942/1946. [ADR-1980]
//! takes it: it built the one prerequisite ADR-1966 named — the datatype rung's
//! own sentence is carried out to whatever the ladder ends on, so the DT
//! blocker census still reads it — and moved the other four assertions to where
//! their guard actually lives, at `check_with_datatype_native` itself.
//!
//! The conversion is selected by `AXEYUM_DATATYPE_NATIVE_REFUSAL`, which is
//! what lets every test below drive **both arms from one binary**. That matters
//! for more than tidiness: this file's own history is that its first fixture was
//! VACUOUS, and a two-arm assertion cannot be — the `propagate` arm has to
//! produce the `Err` and the `decline` arm has to produce something else, in
//! the same process, on the same term.

#![cfg(feature = "full")]

use std::time::Duration;

use axeyum_ir::{Value, eval};
use axeyum_smtlib::parse_script;
use axeyum_solver::{
    CheckResult, DatatypeNativeRefusalPolicy, DatatypeNativeRefusalPolicyGuard, SolverConfig,
    SolverError, solve,
};

/// SITE — `dispatch_uf_fast_paths`'s eager UF+arithmetic rung.
///
/// `check_with_uf_arithmetic` runs `eliminate_functions`, which refuses an
/// array-VALUED uninterpreted function with the sentence "eager Ackermann
/// elimination does not admit array-valued function results; **use canonical
/// AUFBV combination**". The canonical AUFBV combination is
/// `dispatch_abv_online` / `dispatch_array_fast_paths` /
/// `check_with_all_theories` — every one of which sits AFTER this rung. The
/// refusal named the route below it, and the bare `?` is what stopped the
/// query from ever reaching it.
///
/// Satisfiable (`x = 1`, `g(1) = 0`, `f(1)` the constant-zero array).
const ARRAY_VALUED_UF_SAT: &str = "\
(set-logic QF_AUFLIA)
(declare-fun f (Int) (Array Int Int))
(declare-fun g (Int) Int)
(declare-const x Int)
(assert (= (select (f 1) 0) (g x)))
(assert (> x 0))
(check-sat)
";

fn config() -> SolverConfig {
    SolverConfig::new().with_timeout(Duration::from_secs(20))
}

/// Decides `text` and KEEPS the `Err` case.
///
/// An error is precisely what this suite is about, so it must not be flattened
/// into `unknown` by the harness — a helper that mapped `Err` to `Unknown`
/// would make every test here pass on the unfixed tree.
fn decide(text: &str) -> Result<CheckResult, SolverError> {
    let mut script = parse_script(text).expect("script parses");
    solve(&mut script.arena, &script.assertions, &config())
}

#[test]
fn array_valued_uf_refusal_is_not_the_querys_verdict() {
    if let Err(error) = decide(ARRAY_VALUED_UF_SAT) {
        panic!(
            "the eager UF+arithmetic rung's refusal travelled out of `solve` as \
             this query's verdict. Its own sentence says to use the canonical \
             AUFBV combination -- a route BELOW it, which therefore never ran. \
             `unknown` is a first-class result and never an error: {error}"
        );
    }
}

/// SITE — `check_auto_dispatch`'s `check_with_datatype_native` rung (ADR-1980).
///
/// `Lst` has a datatype-typed field, so its tag/field expansion is NOT exact
/// and `collect_ackermann_groups` refuses congruence over `p`'s argument
/// (ADR-1935). Thirteen rungs sit below that refusal.
///
/// **SATISFIABLE, and this is the wrong-`unsat` shape itself.** `x` and `y` are
/// both `cons` with equal heads but unconstrained tails, so they may differ and
/// `p` may differ on them. The inexact encoding ADR-1930 shipped a wrong `unsat`
/// from is exactly the one that would merge them: an antecedent built from the
/// tag and the `hd` field alone, with `tl` dropped because it has no expansion
/// variable, is WEAKER than real equality, which makes the congruence clause
/// STRONGER than the axiom and forces `p x = p y`.
const INEXACT_DATATYPE_CONGRUENCE_SAT: &str = "\
(set-logic QF_UFDT)
(declare-datatypes ((Lst 0)) (((nil) (cons (hd Int) (tl Lst)))))
(declare-fun p (Lst) Bool)
(declare-const x Lst)
(declare-const y Lst)
(assert ((_ is cons) x))
(assert ((_ is cons) y))
(assert (= (hd x) (hd y)))
(assert (p x))
(assert (not (p y)))
(check-sat)
";

/// The same rung's refusal on a query a rung BELOW can actually answer.
///
/// `p` is uninterpreted and `(tl x)` is a single term, so `p := {tl x ↦ true}`
/// is a model and the query is SATISFIABLE. `Lst` is still inexact, so
/// `collect_ackermann_groups` still refuses — this is a decline the ladder
/// recovers from, which is the whole claim.
const INEXACT_DATATYPE_SELECT_ARG_SAT: &str = "\
(set-logic QF_UFDT)
(declare-datatypes ((Lst 0)) (((nil) (cons (hd Int) (tl Lst)))))
(declare-fun p (Lst) Bool)
(declare-const x Lst)
(assert (p (tl x)))
(check-sat)
";

#[test]
fn datatype_rung_refusal_is_not_the_querys_verdict() {
    // TWO ARMS, ONE BINARY, one term — so the fixture cannot be vacuous the way
    // this file's first one was. The `propagate` arm must still produce the
    // `Err`, or the arm below is being compared against nothing.
    let propagated = {
        let _arm = DatatypeNativeRefusalPolicyGuard::set(DatatypeNativeRefusalPolicy::Propagate);
        decide(INEXACT_DATATYPE_SELECT_ARG_SAT)
    };
    assert!(
        matches!(propagated, Err(SolverError::Unsupported(_))),
        "CONTROL FAILED: the `propagate` arm must reproduce the pre-ADR-1980 \
         behaviour, or the arm below is being compared against nothing. Got \
         {propagated:?}"
    );

    // Under the shipped arm a rung below answers, and the model is replayed
    // against the ORIGINAL assertions here rather than trusting the route's own
    // replay.
    let got = decide(INEXACT_DATATYPE_SELECT_ARG_SAT);
    let Ok(CheckResult::Sat(model)) = &got else {
        panic!(
            "the datatype rung's refusal ended this query, so the rungs below it \
             never ran. It is satisfiable at `p := {{tl x -> true}}`: {got:?}"
        );
    };
    let script = parse_script(INEXACT_DATATYPE_SELECT_ARG_SAT).expect("script parses");
    let assignment = model.to_assignment();
    for (n, &assertion) in script.assertions.clone().iter().enumerate() {
        let value = eval(&script.arena, assertion, &assignment);
        assert!(
            matches!(value, Ok(Value::Bool(true))),
            "WRONG SAT: assertion {n} evaluates to {value:?} under the returned model"
        );
    }
}

#[test]
fn a_decline_is_not_a_promise_that_something_below_can_answer() {
    // **MEASURED, and the honest half of ADR-1980.** Converting the site does
    // not turn every refused datatype query into a first-class `unknown`: when
    // no rung below can decide either, the TAIL route refuses in its own right
    // and that refusal still leaves `solve` as an `Err`. So the conversion's
    // value is exactly the files where a lower rung answers, and nothing more —
    // which is why this lane sized itself by an A/B rather than by the blocker
    // count.
    //
    // This is pinned rather than described, because a later change that turns
    // the tail into an `unknown` should have to come here and say so.
    let got = decide(INEXACT_DATATYPE_CONGRUENCE_SAT);
    let Err(SolverError::Unsupported(detail)) = &got else {
        panic!(
            "the tail route now answers this query. That is an improvement, not a \
             failure -- update this test and ADR-1980's finding. Got {got:?}"
        );
    };
    assert!(
        detail.starts_with("congruence over a datatype argument whose expansion is not exact"),
        "even on this path the DATATYPE rung's sentence must lead, or the DT \
         blocker census reads the bit-blast tail instead: {detail}"
    );
}

#[test]
fn datatype_rung_refusal_still_names_its_own_capability() {
    // ADR-1966's ONE named prerequisite. A decline that loses the rung's
    // sentence replaces "congruence over a datatype argument whose expansion is
    // not exact" with the bit-blast tail's "unsupported pure-Rust BV operator",
    // which names the wrong thing — and the DT blocker census is read off
    // exactly these strings, so the census would stop being able to see this
    // capability at all.
    //
    // The fixture is the ADR-1920 cycle: an array whose ELEMENT sort is a
    // datatype, which no rung below can decide either, so the ladder runs out
    // and the reason is observable.
    const ARRAY_OF_DATATYPES: &str = "\
(set-logic QF_AUFDTLIA)
(declare-datatypes ((Color 0)) (((red) (green))))
(declare-const a (Array Int Color))
(declare-const b (Array Int Color))
(declare-const o Color)
(assert (= a (store b 1 o)))
(assert (not (= a b)))
(check-sat)
";
    let got = decide(ARRAY_OF_DATATYPES);
    let Ok(CheckResult::Unknown(reason)) = &got else {
        panic!("expected a first-class `unknown` rather than an error, got {got:?}");
    };
    assert!(
        reason.detail.contains("datatype"),
        "the terminal reason must still carry the DATATYPE rung's sentence, not \
         only the tail route's: {}",
        reason.detail
    );
}

#[test]
fn sound_the_datatype_decline_never_manufactures_an_unsat() {
    // SOUNDNESS-NEGATIVE for the datatype site, and the one that matters: this
    // area shipped two wrong `unsat`s (ADR-1930), both from an inexact datatype
    // encoding, and the plausible wrong answer to this satisfiable query is
    // exactly `unsat`.
    //
    // The conversion must not reach one. It cannot, and the reason is
    // structural rather than incidental: ADR-1980 changed only what the
    // DISPATCHER does with the refusal. `datatype_native`'s exactness
    // preconditions fire on exactly the same queries under both arms, so the
    // inexact congruence clause is never emitted by either. This test is what
    // fails if that ever stops being true.
    let got = decide(INEXACT_DATATYPE_CONGRUENCE_SAT);
    assert!(
        !matches!(got, Ok(CheckResult::Unsat)),
        "WRONG UNSAT: `x` and `y` are both `cons` with equal heads and \
         unconstrained tails, so they may differ and `p` may differ on them. A \
         rung reached past the datatype refusal and merged them: {got:?}"
    );
    // And when it does decide, the model has to satisfy the ORIGINAL assertions.
    // A `sat` that does not is the other half of the same failure, and the
    // route's own replay is part of the subject here.
    if let Ok(CheckResult::Sat(model)) = &got {
        let script = parse_script(INEXACT_DATATYPE_CONGRUENCE_SAT).expect("script parses");
        let assignment = model.to_assignment();
        for (n, &assertion) in script.assertions.clone().iter().enumerate() {
            let value = eval(&script.arena, assertion, &assignment);
            assert!(
                matches!(value, Ok(Value::Bool(true))),
                "WRONG SAT: assertion {n} evaluates to {value:?} under the returned model"
            );
        }
    }
}

#[test]
fn sound_a_declining_ground_rung_never_manufactures_an_unsat() {
    // SOUNDNESS-NEGATIVE, and the reason this change needs one: before the fix
    // the query never reached the rungs below its refusal, so their answers on
    // it were never observed. The fixture is satisfiable (`x = 1`, `g(1) = 0`,
    // `f(1)` the constant-zero array).
    assert!(
        !matches!(decide(ARRAY_VALUED_UF_SAT), Ok(CheckResult::Unsat)),
        "WRONG UNSAT: this query is satisfiable and a rung reached past the \
         refusal refuted it"
    );
}
