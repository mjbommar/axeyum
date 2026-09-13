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
//! # The datatype rung is NOT guarded here, deliberately
//!
//! `check_auto_dispatch`'s `check_with_datatype_native` site is the same shape
//! and is worth **+22 `AUFDTLIRA` files, every one confirmed `unsat` by z3
//! 4.13.3 and cvc5 1.3.4** (`bench-results/dispatch-decline-audit-20260913/`).
//! Converting it turns 7 assertions red in four registered suites owned by
//! ADR-1920/1935/1942/1946 — three of them read the refusal MESSAGE out of that
//! `Err`, because that message is what the blocker census reads. ADR-1966
//! records the measurement and the reason it was not taken. This file does not
//! pretend to guard a site that still has the defect.

#![cfg(feature = "full")]

use std::time::Duration;

use axeyum_smtlib::parse_script;
use axeyum_solver::{CheckResult, SolverConfig, SolverError, solve};

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
