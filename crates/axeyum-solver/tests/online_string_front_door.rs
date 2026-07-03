//! Front-door integration gates for the online CDCL(T) string route (P1.5b).
//!
//! These drive the **text** front door ([`solve_smtlib`]) — and the harness-parity
//! surfaces ([`online_string_verdict`], [`decide_word_only_script`]) — with the
//! census `r1_QF_S_str002` disjunctive shapes: `or`/negated word problems the
//! flat top-level-conjunction word side channel cannot represent. The parser
//! captures their Boolean skeleton in `Script::word_skeleton`, and the online route
//! decides them:
//!
//! ```text
//! (assert (or (= x (str.++ y "aa")) (= x (str.++ y "bb"))))
//! (assert (= x (str.++ y "cc")))          ; each disjunct clashes -> unsat
//! ```
//!
//! The online route only ever *adds* a verdict: `sat` is replay-checked against the
//! original assertions inside the entry point, and `unsat` is a certified theory
//! conflict. It can never override a decided verdict or fabricate a wrong one.

#![allow(clippy::similar_names)]

use std::time::Duration;

use axeyum_smtlib::parse_script;
use axeyum_solver::{
    CheckResult, SolverConfig, decide_word_only_script, online_string_verdict, solve_smtlib,
};

fn cfg() -> SolverConfig {
    SolverConfig {
        timeout: Some(Duration::from_secs(10)),
        ..SolverConfig::default()
    }
}

fn verdict(script: &str) -> CheckResult {
    solve_smtlib(script, &cfg())
        .unwrap_or_else(|e| panic!("solve_smtlib errored: {e:?}"))
        .result
}

// ---------- census-shape UNSAT through the text front door ----------

#[test]
fn front_door_disjunction_of_suffix_constants_unsat() {
    // (or (= x (y++"aa")) (= x (y++"bb"))) ∧ (= x (y++"cc")) — each disjunct is a
    // suffix constant clash after the shared prefix y; the skeleton is Boolean-SAT.
    let s = r#"(set-logic QF_S)
(declare-const x String)
(declare-const y String)
(assert (or (= x (str.++ y "aa")) (= x (str.++ y "bb"))))
(assert (= x (str.++ y "cc")))
(check-sat)"#;
    assert_eq!(verdict(s), CheckResult::Unsat);
}

#[test]
fn front_door_disjunction_of_bare_constants_unsat() {
    // (or (= x "a") (= x "b")) ∧ (= x "c") — two distinct-constant clashes.
    let s = r#"(set-logic QF_S)
(declare-const x String)
(assert (or (= x "a") (= x "b")))
(assert (= x "c"))
(check-sat)"#;
    assert_eq!(verdict(s), CheckResult::Unsat);
}

#[test]
fn front_door_nested_disjunction_unsat() {
    // (or (or (= x "a") (= x "b")) (= x "c")) ∧ (= x "d") — three clashing branches.
    let s = r#"(set-logic QF_S)
(declare-const x String)
(assert (or (or (= x "a") (= x "b")) (= x "c")))
(assert (= x "d"))
(check-sat)"#;
    assert_eq!(verdict(s), CheckResult::Unsat);
}

#[test]
fn front_door_disjunction_with_negated_equality_unsat() {
    // (or (= x (y++"a")) (= z (y++"a"))) ∧ (= x (y++"a")) ∧ (= z (y++"a"))
    //  ∧ (not (= x z))  — x ≈ z contradicts the disequality.
    let s = r#"(set-logic QF_S)
(declare-const x String)
(declare-const y String)
(declare-const z String)
(assert (or (= x (str.++ y "a")) (= z (str.++ y "a"))))
(assert (= x (str.++ y "a")))
(assert (= z (str.++ y "a")))
(assert (not (= x z)))
(check-sat)"#;
    assert_eq!(verdict(s), CheckResult::Unsat);
}

// ---------- census-shape SAT through the text front door ----------

#[test]
fn front_door_disjunction_consistent_branch_sat() {
    // (or (= x (y++"aa")) (= x (y++"bb"))) ∧ (= x (y++"aa")) — branch 1 holds.
    let s = r#"(set-logic QF_S)
(declare-const x String)
(declare-const y String)
(assert (or (= x (str.++ y "aa")) (= x (str.++ y "bb"))))
(assert (= x (str.++ y "aa")))
(check-sat)"#;
    assert!(
        matches!(verdict(s), CheckResult::Sat(_)),
        "the consistent-branch disjunction must decide sat"
    );
}

#[test]
fn front_door_bare_constant_disjunction_consistent_branch_sat() {
    // (or (= x "a") (= x "b")) ∧ (= x "a").
    let s = r#"(set-logic QF_S)
(declare-const x String)
(assert (or (= x "a") (= x "b")))
(assert (= x "a"))
(check-sat)"#;
    assert!(matches!(verdict(s), CheckResult::Sat(_)));
}

// ---------- over-cap (word-first fallback) disjunctive shapes ----------
//
// String literals over `STRING_MAX_LEN` (8) make the *bounded* parse decline, so
// the script arrives via the word-first fallback with an empty flat view and a
// `word_skeleton`-only side channel. The online route (through
// `decide_word_only_script`) decides it — a verdict the bounded encoder never
// reaches. Before P1.5b these were a bare `unsupported`.

#[test]
fn front_door_overcap_disjunction_unsat() {
    let s = r#"(set-logic QF_S)
(declare-const x String)
(declare-const y String)
(assert (or (= x (str.++ y "aaaaaaaaaa")) (= x (str.++ y "bbbbbbbbbb"))))
(assert (= x (str.++ y "cccccccccc")))
(check-sat)"#;
    assert_eq!(verdict(s), CheckResult::Unsat);
    // And directly through the word-first-fallback harness surface.
    let mut script = parse_script(s).expect("parse over-cap word-first fallback");
    assert!(script.word_only_fallback.is_some());
    assert!(!script.word_skeleton.is_empty());
    assert_eq!(
        decide_word_only_script(&mut script, &cfg()).expect("decide word-only"),
        CheckResult::Unsat,
    );
}

// ---------- the online harness surface decides the skeleton directly ----------

#[test]
fn online_string_verdict_decides_disjunctive_skeleton() {
    let s = r#"(set-logic QF_S)
(declare-const x String)
(declare-const y String)
(assert (or (= x (str.++ y "aa")) (= x (str.++ y "bb"))))
(assert (= x (str.++ y "cc")))
(check-sat)"#;
    let mut script = parse_script(s).expect("parse disjunctive skeleton");
    assert!(
        !script.word_skeleton.is_empty(),
        "the disjunctive shape must populate the Boolean word skeleton"
    );
    assert_eq!(
        online_string_verdict(&mut script, &cfg()),
        Some(CheckResult::Unsat),
    );
}

// ---------- scope: a non-string script never populates the skeleton ----------

#[test]
fn non_string_script_has_no_word_skeleton() {
    let s = r"(set-logic QF_BV)
(declare-const a (_ BitVec 8))
(declare-const b (_ BitVec 8))
(assert (or (= a b) (= a #x00)))
(check-sat)";
    let mut script = parse_script(s).expect("parse bv script");
    assert!(
        script.word_skeleton.is_empty(),
        "a bit-vector script must not populate the word skeleton"
    );
    // And the online harness surface declines it.
    assert_eq!(online_string_verdict(&mut script, &cfg()), None);
}

// ---------- soundness: a satisfiable disjunctive script is never unsat ----------

#[test]
fn front_door_never_wrong_unsat_on_sat_disjunction() {
    // (or (= x "a") (= x "b")) with no clashing conjunct — clearly SAT; must never
    // be reported unsat by any route.
    let s = r#"(set-logic QF_S)
(declare-const x String)
(assert (or (= x "a") (= x "b")))
(check-sat)"#;
    match verdict(s) {
        CheckResult::Unsat => panic!("WRONG UNSAT on a satisfiable disjunction — a soundness bug"),
        CheckResult::Sat(_) | CheckResult::Unknown(_) => {}
    }
}
