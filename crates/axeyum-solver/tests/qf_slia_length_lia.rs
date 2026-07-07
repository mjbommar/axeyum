//! Focused tests for the **length↔LIA `sat` bridge** (P2.7 Phase A, `LenAbs`) — the
//! `str.len`-coupled `QF_SLIA` second-chance route
//! ([`length_lia_verdict`](axeyum_solver::length_lia_verdict) / the `solve_smtlib`
//! front door). The route links `str.len` to the LIA solver over fresh per-variable
//! length symbols and adds a **replay-checked `sat`** for rows whose witness the
//! bounded packed encoder cannot represent (its length is capped at `STRING_MAX_LEN`),
//! e.g. `(= (str.len x) 20)`.
//!
//! Soundness bars exercised here (strings + arithmetic is doubly error-prone):
//! - a `sat` length-coupled query decides (via the length route specifically) and its
//!   model is `Seq`-level replay-checked by construction (`solve_smtlib` `Sat`);
//! - an `unsat` length-coupled query still decides `unsat` (the ADR-0052 `StringGate`
//!   owns that; the length route is strictly additive and must not regress it);
//! - a `sat` query the `'a'`-fill cannot witness (content-distinct equal-length
//!   strings) degrades to `unknown` — **never** a wrong `unsat` and never a wrong
//!   `sat`.

use std::time::Duration;

use axeyum_smtlib::parse_script;
use axeyum_solver::{CheckResult, SolverConfig, length_lia_verdict, solve_smtlib};

fn cfg() -> SolverConfig {
    SolverConfig::new().with_timeout(Duration::from_secs(5))
}

/// The length route itself decides `(= (str.len x) 20)` — a `sat` whose 20-char
/// witness exceeds the bounded encoder's length cap.
#[test]
fn length_route_decides_bare_length_equality_sat() {
    let s = "(set-logic QF_SLIA)\n\
             (declare-fun x () String)\n\
             (assert (= (str.len x) 20))\n\
             (check-sat)\n";
    let mut script = parse_script(s).expect("parse bare length equality");
    // The length route specifically produces the verdict.
    assert!(
        matches!(
            length_lia_verdict(&mut script, &cfg()),
            Some(CheckResult::Sat(_))
        ),
        "length route must add a replay-checked sat for str.len x = 20"
    );
    // And the front door reports it (previously `unknown`).
    let out = solve_smtlib(s, &cfg()).expect("solve");
    assert!(matches!(out.result, CheckResult::Sat(_)), "front door sat");
}

/// A concatenation length system coupled with integer constants:
/// `z = x ++ y ∧ len x = 20 ∧ len y = 5 ∧ len z = 25`. The `'a'`-fill is
/// length-homomorphic, so `z = x ++ y` holds in the witness and it replays.
#[test]
fn length_route_decides_concat_length_system_sat() {
    let s = "(set-logic QF_SLIA)\n\
             (declare-fun x () String)\n\
             (declare-fun y () String)\n\
             (declare-fun z () String)\n\
             (assert (= z (str.++ x y)))\n\
             (assert (= (str.len x) 20))\n\
             (assert (= (str.len y) 5))\n\
             (assert (= (str.len z) 25))\n\
             (check-sat)\n";
    let mut script = parse_script(s).expect("parse concat length system");
    assert!(
        matches!(
            length_lia_verdict(&mut script, &cfg()),
            Some(CheckResult::Sat(_))
        ),
        "length route must witness the concat length system"
    );
    let out = solve_smtlib(s, &cfg()).expect("solve");
    assert!(matches!(out.result, CheckResult::Sat(_)), "front door sat");
}

/// A free `Int` variable coupled to a string length: `n = str.len x ∧ n = 30`.
/// The route must bind `n` from the LIA model and `x` to a 30-char `'a'`-fill.
#[test]
fn length_route_decides_free_int_coupling_sat() {
    let s = "(set-logic QF_SLIA)\n\
             (declare-fun x () String)\n\
             (declare-fun n () Int)\n\
             (assert (= n (str.len x)))\n\
             (assert (= n 30))\n\
             (check-sat)\n";
    let out = solve_smtlib(s, &cfg()).expect("solve");
    assert!(
        matches!(out.result, CheckResult::Sat(_)),
        "free-int-coupled length query must decide sat"
    );
}

/// A Boolean-structured length constraint: `len x = 12 ∨ len x = 15` — a disjunction
/// over the (over-cap) lengths, still `sat`.
#[test]
fn length_route_decides_disjunctive_length_sat() {
    let s = "(set-logic QF_SLIA)\n\
             (declare-fun x () String)\n\
             (assert (or (= (str.len x) 12) (= (str.len x) 15)))\n\
             (check-sat)\n";
    let out = solve_smtlib(s, &cfg()).expect("solve");
    assert!(
        matches!(out.result, CheckResult::Sat(_)),
        "disjunctive length sat"
    );
}

/// The length route is **additive**: a genuinely-`unsat` length-coupled query still
/// decides `unsat` (the ADR-0052 `StringGate` owns it; the route must not regress it).
#[test]
fn unsat_length_query_still_decides_unsat() {
    for s in [
        // len x = 20 ∧ len x < 5  (over-cap linear contradiction).
        "(set-logic QF_SLIA)\n(declare-fun x () String)\n\
         (assert (= (str.len x) 20))\n(assert (< (str.len x) 5))\n(check-sat)\n",
        // len(x ++ y) < len(x): impossible (len non-negative).
        "(set-logic QF_SLIA)\n(declare-fun x () String)\n(declare-fun y () String)\n\
         (assert (< (str.len (str.++ x y)) (str.len x)))\n(check-sat)\n",
        // n = str.len x ∧ n > 100 ∧ n < 50 (over-cap free-int contradiction).
        "(set-logic QF_SLIA)\n(declare-fun x () String)\n(declare-fun n () Int)\n\
         (assert (= n (str.len x)))\n(assert (> n 100))\n(assert (< n 50))\n(check-sat)\n",
    ] {
        let out = solve_smtlib(s, &cfg()).expect("solve");
        assert_eq!(
            out.result,
            CheckResult::Unsat,
            "length-coupled unsat must still decide unsat:\n{s}"
        );
    }
}

/// A `sat` query the `'a'`-fill cannot witness — two content-distinct strings of the
/// same over-cap length (`x ≠ y ∧ len x = 20 ∧ len y = 20`, really `sat` with
/// e.g. `x = a…a`, `y = a…ab`). The route must **decline to `unknown`**, never a wrong
/// `unsat` and never a wrong `sat`.
#[test]
fn content_distinct_equal_length_declines_to_unknown() {
    let s = "(set-logic QF_SLIA)\n\
             (declare-fun x () String)\n\
             (declare-fun y () String)\n\
             (assert (not (= x y)))\n\
             (assert (= (str.len x) 20))\n\
             (assert (= (str.len y) 20))\n\
             (check-sat)\n";
    let out = solve_smtlib(s, &cfg()).expect("solve");
    assert!(
        matches!(out.result, CheckResult::Unknown(_)),
        "content-distinct equal-length query must decline to unknown (a sound miss), \
         got {:?}",
        out.result
    );
}

/// The route does **not** fire on a non-`str.len` string script (no length skeleton):
/// a pure word-equation problem carries no `length_skeleton`, so the length verdict
/// is `None`.
#[test]
fn no_length_skeleton_yields_none() {
    let s = "(set-logic QF_S)\n\
             (declare-fun x () String)\n\
             (assert (= x (str.++ x \"a\")))\n\
             (check-sat)\n";
    let mut script = parse_script(s).expect("parse word problem");
    assert_eq!(length_lia_verdict(&mut script, &cfg()), None);
}
