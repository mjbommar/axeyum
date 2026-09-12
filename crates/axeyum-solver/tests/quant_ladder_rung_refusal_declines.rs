//! A quantified-ladder rung's FRAGMENT refusal must not become the query's
//! verdict.
//!
//! # What was wrong
//!
//! `solve`'s quantified ladder has twenty rungs. Four of them ran a
//! *speculative sub-solve* over a REWRITTEN query — a canonicalized form, a
//! quantifier-erased skeleton, `not body[x := c]` for a validity check, an MBQI
//! ground round — and propagated that sub-solve's `SolverError::Unsupported`
//! with `?`. So a rung whose sub-query fell outside some backend's fragment
//! ended the whole dispatch: `solve` returned `Err(Unsupported)` and every rung
//! below it never ran.
//!
//! Measured 2026-09-12 on the SMT-LIB `AUFDTLIRA` division (11,043 files): a
//! 200-file stride sample stopped at `attempts=2` after ~1 ms on
//! `eager Ackermann elimination does not admit array-valued function results`
//! — a sentence about a quantifier-erased SKELETON — and the division scored
//! **0 of 200** on the 24 s parity board while z3 and cvc5 each scored 176.
//! With the refusals declining instead, the same binary decides **62 of 200**
//! (ab-AUFDTLIRA, 10 s), every one of them agreeing with the file's declared
//! `:status`.
//!
//! [`crate::auto::ground_subset_refutes_quantified_query`], the rung directly
//! above these, already had the rule in its own words — "this is an optional
//! accelerator; it must never turn a query the established portfolio can handle
//! into an operational error". The rungs below it had the same contract and not
//! the guard.
//!
//! # What these tests pin
//!
//! The fixtures are the smallest shape that reproduces the division's refusal:
//! a datatype with an **array-typed field** (`array/UF datatype fields are not
//! yet supported (ADR-0022)`) under a quantifier. They are deliberately not
//! about datatypes — the guard is about the ladder — but a synthetic query that
//! no rung refuses would test nothing.
//!
//! * [`a_refused_rung_does_not_answer_a_query_a_later_rung_decides`] is the
//!   positive control: the query's contradiction is `x > 0 AND x < 0`, so its
//!   `unsat` is not in doubt (cvc5 1.3.4 and z3 both agree), and before the
//!   guards `solve` returned `Err(Unsupported)` on it.
//! * [`a_refused_rung_yields_a_first_class_unknown_not_an_error`] is the same
//!   shape with no reachable refutation: the ladder must run to the end and
//!   report `unknown`, which "is a first-class solver result, never an error".
//! * [`sound_a_declining_rung_never_manufactures_an_unsat`] is the
//!   soundness-negative: the same shape, **satisfiable** (z3: `sat`). Letting
//!   more rungs run is only sound if none of them answers `unsat` here. This
//!   test fails on any change that trades the refusal for a wrong refutation.

#![cfg(feature = "full")]

use std::time::Duration;

use axeyum_smtlib::parse_script;
use axeyum_solver::{CheckResult, SolverConfig, solve};

/// A datatype whose single field is an `(Array Int Int)` — the shape
/// `datatype_native` refuses — under a universal, plus a ground contradiction
/// that any arithmetic rung refutes on its own.
const ARRAY_FIELD_UNSAT: &str = "\
(set-logic AUFDTLIRA)
(declare-datatypes ((Box 0)) (((mk (contents (Array Int Int))))))
(declare-const b Box)
(declare-const x Int)
(assert (forall ((i Int)) (>= (select (contents b) i) 0)))
(assert (> x 0))
(assert (< x 0))
(check-sat)
";

/// The same shape with no ground contradiction and a refutation that needs the
/// universal instantiated at `3` — which no rung in the ladder reaches today.
const ARRAY_FIELD_UNDECIDED: &str = "\
(set-logic AUFDTLIRA)
(declare-datatypes ((Box 0)) (((mk (contents (Array Int Int))))))
(declare-const b Box)
(assert (forall ((i Int)) (>= (select (contents b) i) 0)))
(assert (< (select (contents b) 3) 0))
(check-sat)
";

/// The same shape, satisfiable.
const ARRAY_FIELD_SAT: &str = "\
(set-logic AUFDTLIRA)
(declare-datatypes ((Box 0)) (((mk (contents (Array Int Int))))))
(declare-const b Box)
(declare-const x Int)
(assert (forall ((i Int)) (>= (select (contents b) i) 0)))
(assert (> x 0))
(check-sat)
";

fn config() -> SolverConfig {
    SolverConfig::new().with_timeout(Duration::from_secs(20))
}

/// Decides `text`, keeping the `Err` case: an error is precisely what these
/// tests are about, so it must not be flattened into `unknown` by the harness.
fn decide(text: &str) -> Result<CheckResult, axeyum_solver::SolverError> {
    let mut script = parse_script(text).expect("script parses");
    solve(&mut script.arena, &script.assertions, &config())
}

#[test]
fn a_refused_rung_does_not_answer_a_query_a_later_rung_decides() {
    match decide(ARRAY_FIELD_UNSAT) {
        Ok(CheckResult::Unsat) => {}
        other => panic!(
            "a query whose contradiction is `x > 0 AND x < 0` must be refuted; \
             a rung's fragment refusal answered it instead: {other:?}"
        ),
    }
}

#[test]
fn a_refused_rung_yields_a_first_class_unknown_not_an_error() {
    // `Unsat` is admitted alongside `Unknown` on purpose: a later rung learning
    // to refute this would be a capability gain, not a failure of this guard.
    // What must not happen is an ERROR.
    match decide(ARRAY_FIELD_UNDECIDED) {
        Ok(CheckResult::Unknown(_) | CheckResult::Unsat) => {}
        other => panic!(
            "an undecided query must reach a first-class `unknown`, not an \
             error: {other:?}"
        ),
    }
}

#[test]
fn sound_a_declining_rung_never_manufactures_an_unsat() {
    // SOUNDNESS-NEGATIVE. Running more rungs is only sound if none of them
    // refutes a satisfiable query. z3 answers `sat` here.
    let outcome = decide(ARRAY_FIELD_SAT);
    assert!(
        !matches!(outcome, Ok(CheckResult::Unsat)),
        "WRONG UNSAT: this query is satisfiable (x = 1, every array cell 0) and \
         a rung reached past the refusal refuted it"
    );
}
