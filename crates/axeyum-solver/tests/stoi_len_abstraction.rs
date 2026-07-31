//! The `str.to_int`-aware length/value abstraction (P2.7 A.2 `to_int`↔LIA) and
//! its supporting parse-level normalizations, targeted at the
//! `2019-full_str_int` `QF_SLIA` family whose bounded solves ended at
//! "no model within the bounded integer width" `unknown`:
//!
//! - **`to_int` value/length coupling** (`LenAbs::note_stoi_bridge`): the sound
//!   linear consequences of cvc5 `StringsPreprocess::reduce` `STRING_STOI` /
//!   Z3 `seq_axioms` — `t ≥ -1`, `len(s) = 0 → t = -1`, and
//!   `len(s) ≤ k → t ≤ 10^k - 1` for `k = 1..=9`.
//! - **ground Int constant folding** at parse (`ground_int_fold`): generated
//!   corpora spell the same constant many ways (`(+ (+ 1 1) (+ (+ 1 1) 1))`
//!   vs `(+ (+ (+ 1 1) (+ 1 1)) 1)`), hiding `A ∧ ¬A` from hash-consing.
//! - **semantic suffix view** (`semantic_suffix_count`): the exact length of
//!   `substr(s, d, len(s) - d)` recorded spelling-immune.
//! - **`str.at`-over-substr folding** (`LenAbs::substr_view`):
//!   `at(substr(X, i, k), j) = at(X, i + j)` for ground `i ≥ 0`, `0 ≤ j < k`.
//! - **step-1b BV-free projection** (`StringGate::confirm`): pure-Bool glue
//!   assertions (kaluza `T_5 = ¬T_4` chains) are kept in a projection the
//!   exact Bool+LIA refuters decide.
//!
//! Every `unsat` expectation below was cross-checked against cvc5 before
//! landing (and the 12-file corpus bucket this closes is cvc5-verified,
//! DISAGREE = 0). The SOUNDNESS tests lock the sat side: the abstraction must
//! never refute a really-satisfiable query.
#![cfg(feature = "full")]

use std::time::Duration;

use axeyum_solver::{CheckResult, SolverConfig, solve_smtlib};

fn config() -> SolverConfig {
    SolverConfig::new().with_timeout(Duration::from_secs(30))
}

fn verdict(text: &str) -> CheckResult {
    solve_smtlib(text, &config()).expect("decides").result
}

/// `to_int(str.at s i)` is at most 9 (`len(str.at) ≤ 1`), so `≥ 10` refutes —
/// the exact `full_str_int` `247.smt2` core shape (cvc5: unsat).
#[test]
fn to_int_of_at_ge_ten_is_unsat() {
    let text = "(set-logic QF_SLIA)\n(declare-fun s () String)\n\
                (assert (>= (str.to_int (str.at s 3)) 10))\n(check-sat)\n";
    assert_eq!(verdict(text), CheckResult::Unsat);
}

/// Degenerate operand (Hard Rule): `to_int(\"\") = -1` exactly, so an empty
/// string with `to_int = 0` refutes (cvc5: unsat).
#[test]
fn to_int_of_empty_is_minus_one() {
    let text = "(set-logic QF_SLIA)\n(declare-fun s () String)\n\
                (assert (= (str.len s) 0))\n(assert (= (str.to_int s) 0))\n(check-sat)\n";
    assert_eq!(verdict(text), CheckResult::Unsat);
}

/// A 3-char string's `to_int` is at most `10^3 - 1 = 999` (cvc5: unsat).
#[test]
fn to_int_exceeding_length_capacity_is_unsat() {
    let text = "(set-logic QF_SLIA)\n(declare-fun s () String)\n\
                (assert (= (str.len s) 3))\n(assert (= (str.to_int s) 1000))\n(check-sat)\n";
    assert_eq!(verdict(text), CheckResult::Unsat);
}

/// SOUNDNESS boundary: `999` IS reachable by a 3-char string — the coupling
/// facts must not over-tighten (cvc5: sat, witness "999").
#[test]
fn to_int_at_capacity_boundary_is_sat() {
    let text = "(set-logic QF_SLIA)\n(declare-fun s () String)\n\
                (assert (= (str.len s) 3))\n(assert (= (str.to_int s) 999))\n(check-sat)\n";
    assert!(matches!(verdict(text), CheckResult::Sat(_)));
}

/// SOUNDNESS: non-digit strings give `-1`; the abstraction leaves the value
/// free besides the length coupling (cvc5: sat, witness e.g. "ab").
#[test]
fn to_int_minus_one_of_nondigits_is_sat() {
    let text = "(set-logic QF_SLIA)\n(declare-fun s () String)\n\
                (assert (= (str.len s) 2))\n(assert (= (str.to_int s) (- 1)))\n(check-sat)\n";
    assert!(matches!(verdict(text), CheckResult::Sat(_)));
}

/// SOUNDNESS: leading zeros are valid (`to_int(\"000\") = 0`); a lower bound
/// from the length would be a wrong-unsat trap (cvc5: sat).
#[test]
fn to_int_zero_with_leading_zeros_is_sat() {
    let text = "(set-logic QF_SLIA)\n(declare-fun s () String)\n\
                (assert (= (str.len s) 3))\n(assert (= (str.to_int s) 0))\n(check-sat)\n";
    assert!(matches!(verdict(text), CheckResult::Sat(_)));
}

/// The semantic suffix view: `len(substr(s, 7, len(s) - 7)) = 1` forces
/// `len(s) = 8`, contradicting `len(s) > 8` — with the `7`s spelled as
/// *different* compound constant arithmetic, so only the spelling-immune
/// (post-folding, term-identity) matcher can see the suffix shape — the
/// `full_str_int` `4868.smt2` core (cvc5: unsat).
#[test]
fn semantic_suffix_length_conflict_is_unsat() {
    let text = "(set-logic QF_SLIA)\n(declare-fun s () String)\n\
                (assert (> (str.len s) 8))\n\
                (assert (= (str.len (str.substr s (+ 3 4) (- (str.len s) (+ (+ 1 1 1) 4)))) 1))\n\
                (check-sat)\n";
    assert_eq!(verdict(text), CheckResult::Unsat);
}

/// SOUNDNESS: the same shape with `len(s) = 8` has the suffix length exactly 1
/// (cvc5: sat) — the exact expression must not over-refute.
#[test]
fn semantic_suffix_length_fit_is_sat() {
    let text = "(set-logic QF_SLIA)\n(declare-fun s () String)\n\
                (assert (= (str.len s) 8))\n\
                (assert (= (str.len (str.substr s (+ 3 4) (- (str.len s) (+ 3 4)))) 1))\n\
                (check-sat)\n";
    assert!(matches!(verdict(text), CheckResult::Sat(_)));
}

/// `at(substr(s,0,3),0)` and `at(substr(s,0,2),0)` are the same absolute
/// position `at(s,0)`; asserting `= \"0\"` for one and `≠ \"0\"` for the other
/// refutes — the `full_str_int` `2959.smt2` core (cvc5: unsat).
#[test]
fn at_over_substr_same_position_conflict_is_unsat() {
    let text = "(set-logic QF_SLIA)\n(declare-fun s () String)\n\
                (assert (= (str.at (str.substr s 0 3) 0) \"0\"))\n\
                (assert (not (= (str.at (str.substr s 0 2) 0) \"0\")))\n(check-sat)\n";
    assert_eq!(verdict(text), CheckResult::Unsat);
}

/// SOUNDNESS guards on the fold: a negative substr offset means the substring
/// is empty (`at` of it is `\"\"`), and the fold must NOT rewrite to
/// `at(s, -1)`-style absolute positions; likewise `j ≥ k` is out of range on
/// the substring even when `s` itself is longer. Both are sat (cvc5: sat).
#[test]
fn at_over_substr_out_of_range_guards_are_sat() {
    for text in [
        "(set-logic QF_SLIA)\n(declare-fun s () String)\n\
         (assert (= (str.at (str.substr s (- 0 1) 2) 0) \"\"))\n(check-sat)\n",
        "(set-logic QF_SLIA)\n(declare-fun s () String)\n\
         (assert (= (str.at (str.substr s 0 2) 2) \"\"))\n(check-sat)\n",
    ] {
        assert!(
            matches!(verdict(text), CheckResult::Sat(_)),
            "out-of-range at-over-substr must stay sat: {text}"
        );
    }
}

/// Ground Int constant folding: the two `≤ 255` atoms differ only in the
/// spelling of the constant `5`, so folding makes them the *same* atom and
/// `A ∧ ¬A` refutes — the `full_str_int` `3640.smt2` core (cvc5: unsat).
#[test]
fn constant_spelling_folding_exposes_contradiction() {
    let text = "(set-logic QF_SLIA)\n(declare-fun s () String)\n\
                (assert (<= (str.to_int (str.substr s (+ (+ 1 1) (+ (+ 1 1) 1)) 2)) 255))\n\
                (assert (not (<= (str.to_int (str.substr s (+ (+ (+ 1 1) (+ 1 1)) 1) 2)) 255)))\n\
                (check-sat)\n";
    assert_eq!(verdict(text), CheckResult::Unsat);
}

/// Step-1b BV-free projection: kaluza-style pure-Bool glue (`T_5 = ¬T_4`)
/// carries no `Int`, so the Int-mentions projection drops it — the BV-free
/// projection keeps it and refutes (cvc5: unsat; the
/// `17020.corecstrs.readable.smt2` core).
#[test]
fn bool_glue_atom_conflict_is_unsat() {
    let text = "(set-logic QF_SLIA)\n(declare-fun v () String)\n\
                (declare-fun t4 () Bool)\n(declare-fun t5 () Bool)\n(declare-fun td () Bool)\n\
                (assert (= t4 (= \"-\" v)))\n(assert (= t5 (not t4)))\n(assert t5)\n\
                (assert (= td (= \"-\" v)))\n(assert td)\n(check-sat)\n";
    assert_eq!(verdict(text), CheckResult::Unsat);
}

/// SOUNDNESS (never-wrong locks, full literal grammar): shapes the route does
/// not decide today must stay `sat`-or-`unknown`, never `unsat`. The second
/// query pins a `\\u{...}`-escaped literal above `0xFF` next to the `to_int`
/// coupling (the escape-grammar rule for string generators/tests).
#[test]
fn undecided_shapes_are_never_wrongly_unsat() {
    for text in [
        // Reflexive disequality through two substr views (semantically unsat;
        // decided or honest-unknown, never sat).
        "(set-logic QF_SLIA)\n(declare-fun s () String)\n\
         (assert (not (= (str.at (str.substr s 0 3) 0) (str.at s 0))))\n(check-sat)\n",
        // Unicode-escape literal above the byte range with a to_int coupling —
        // really sat (witness s = \"\\u{300}\"), must never be refuted.
        "(set-logic QF_SLIA)\n(declare-fun s () String)\n\
         (assert (= (str.len s) 1))\n(assert (= (str.to_int s) (- 1)))\n\
         (assert (str.< \"\\u{2FF}\" s))\n(check-sat)\n",
    ] {
        // A clean parse-level decline (`Err`) is an acceptable non-verdict —
        // the byte-model front end may reject `\u{...}` literals above `0xFF`
        // outright (ADR-0029); only a *wrong verdict* fails this lock.
        let Ok(out) = solve_smtlib(text, &config()) else {
            continue;
        };
        if text.contains("str.<") {
            assert!(
                matches!(out.result, CheckResult::Sat(_) | CheckResult::Unknown(_)),
                "really-sat query must never be unsat: {text}"
            );
        } else {
            assert!(
                matches!(out.result, CheckResult::Unsat | CheckResult::Unknown(_)),
                "really-unsat query must never be sat: {text}"
            );
        }
    }
}
