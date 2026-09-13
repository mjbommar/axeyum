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
//! `scripts/enumerate-dispatch-refusal-propagation.py`, not by reading.
//!
//! # Both fixtures are DISCRIMINATING, and that was not free
//!
//! The obvious fixture — the refusing shape plus a ground contradiction
//! `x > 0 AND x < 0` — is **vacuous here**, and was written and thrown away
//! before this file reached its present form. `int-box-eval` refutes such a
//! query at `attempts=3`, long before the ladder reaches the rung under test,
//! so both arms answer `unsat` and the test passes on the unfixed tree. Each
//! fixture below was instead checked against a binary built WITHOUT the guards
//! and kept only because the two arms differ:
//!
//! | fixture | without the guards | with them |
//! |---|---|---|
//! | [`ARRAY_VALUED_UF_SAT`] | `Err`, `attempts=17` | `Ok(Unknown)`, `attempts=20` |
//! | [`DATATYPE_UF_ARGUMENT`] | `Err(… ADR-0022)`, `attempts=6` | a different refusal, `attempts=30` |
//!
//! `DATATYPE_UF_ARGUMENT` is the reason
//! [`datatype_native_refusal_is_no_longer_the_querys_answer`] asserts on the
//! MESSAGE rather than on `Ok`: with the guard the ladder runs twenty-four more
//! rungs and then meets a SEPARATE terminal refusal in the bit-blast tail
//! (`unsupported pure-Rust BV operator DtTest`). That second refusal is real,
//! is recorded in ADR-1966 as remaining work, and is not this guard's subject.
//! A test that demanded `Ok` here would be asserting a capability nobody
//! claimed, and would fail for the wrong reason.

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

/// SITE — `check_auto_dispatch`'s datatype branch.
///
/// `datatype_elim` refuses (a free datatype variable survives), and then
/// `check_with_datatype_native` refuses congruence over a datatype argument
/// whose expansion is not exact (ADR-0022) — a refusal ADR-1927's own
/// after-census measured as one of the top blockers of the `*DT*` divisions.
/// That second refusal was returned with `?`, so it became the query's answer
/// and the thirteen rungs below the datatype branch never ran.
///
/// Satisfiable (`a = cons(1, b)`, `b = nil`, `p(a) = 1`, `p(b) = 0`).
const DATATYPE_UF_ARGUMENT: &str = "\
(set-logic QF_UFDT)
(declare-datatypes ((Lst 0)) (((cons (hd Int) (tl Lst)) (nil))))
(declare-fun p (Lst) Int)
(declare-const a Lst)
(declare-const b Lst)
(assert ((_ is cons) a))
(assert (= (tl a) b))
(assert (> (p a) (p b)))
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
    match decide(ARRAY_VALUED_UF_SAT) {
        Err(error) => panic!(
            "the eager UF+arithmetic rung's refusal travelled out of `solve` as \
             this query's verdict. Its own sentence says to use the canonical \
             AUFBV combination -- a route BELOW it, which therefore never ran. \
             `unknown` is a first-class result and never an error: {error}"
        ),
        Ok(_) => {}
    }
}

#[test]
fn datatype_native_refusal_is_no_longer_the_querys_answer() {
    // Asserts on the MESSAGE, not on `Ok`: see the module note. What must not
    // happen is that the DATATYPE rung's refusal is the answer; a later,
    // different refusal is a separate (recorded) gap, not a regression here.
    if let Err(SolverError::Unsupported(message)) = decide(DATATYPE_UF_ARGUMENT)
        && message.contains("ADR-0022")
    {
        panic!(
            "the datatype-native rung's refusal is still this query's answer, \
             so the thirteen rungs below the datatype branch never ran: \
             {message}"
        );
    }
}

#[test]
fn sound_a_declining_ground_rung_never_manufactures_an_unsat() {
    // SOUNDNESS-NEGATIVE, and the reason this change needs one: before the fix
    // neither query reached the rungs below its refusal, so those rungs'
    // answers on them were never observed. BOTH fixtures are satisfiable.
    for (name, text) in [
        ("array-valued UF", ARRAY_VALUED_UF_SAT),
        ("datatype UF argument", DATATYPE_UF_ARGUMENT),
    ] {
        assert!(
            !matches!(decide(text), Ok(CheckResult::Unsat)),
            "WRONG UNSAT on {name}: this query is satisfiable and a rung \
             reached past the refusal refuted it"
        );
    }
}
