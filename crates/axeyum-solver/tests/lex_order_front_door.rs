//! Front-door integration gates for the lexicographic-order string route
//! (P2.7 T-C.6): the `str.<=` / `str.<` second chance that certifies the reachable
//! lex fragment the ADR-0052 [`StringGate`] previously downgraded to `unknown`.
//!
//! Two census shapes drive it:
//!
//! - **`r0…leq`** — a disjunction of always-true / always-false lex atoms over
//!   constant-prefixed concatenations, `unsat` by variable-independent constant
//!   folding of the Boolean skeleton;
//! - **`r1…leq-trans-unsat`** — `x ≤ y ∧ y ≤ w ∧ x = "G"++xp ∧ w = "E"`, `unsat` by
//!   transitivity (`x ≤ w`) plus the first-character clash `lead(x) = 71 > 69`.
//!
//! The route only ever *adds* a re-checked `unsat` to an `unknown`; satisfiable lex
//! scripts are decided by the bounded encoder and pass through untouched.

use std::time::Duration;

use axeyum_smtlib::parse_script;
use axeyum_solver::{CheckResult, SolverConfig, lex_order_verdict, solve_smtlib};

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

#[test]
fn front_door_leq_transitivity_first_char_clash_unsat() {
    // x ≤ y ∧ y ≤ w ∧ x = "G"++xp ∧ w = "E". Transitivity ⇒ x ≤ "E", but lead(x)=71
    // > 69 = lead("E") and x is not a prefix of "E" ⇒ contradiction.
    let s = r#"(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(declare-fun z () String)
(declare-fun w () String)
(assert (str.<= x y))
(assert (str.<= y w))
(declare-fun xp () String)
(assert (= x (str.++ "G" xp)))
(assert (= w "E"))
(check-sat)"#;
    assert_eq!(verdict(s), CheckResult::Unsat);
}

#[test]
fn front_door_leq_disjunction_constant_fold_unsat() {
    // (or (not A1) (not A2) A3): A1,A2 always true (65<66 at pos 0), A3 always false
    // ("AD..." > "AC..."); the disjunction folds to false.
    let s = r#"(set-logic QF_SLIA)
(declare-const x String)
(declare-const y String)
(assert (or
  (not (str.<= (str.++ "A" x) (str.++ "B" y)))
  (not (str.<= (str.++ "A" x) (str.++ "BC" y)))
  (str.<= (str.++ "A" "D" x) (str.++ "AC" y))))
(check-sat)"#;
    assert_eq!(verdict(s), CheckResult::Unsat);
}

#[test]
fn front_door_strict_less_first_char_clash_unsat() {
    // x < w ∧ x = "Z"++xp ∧ w = "A": lead(x)=90 > 65 = lead("A") ⇒ contradiction.
    let s = r#"(set-logic QF_SLIA)
(declare-const x String)
(declare-const w String)
(declare-const xp String)
(assert (str.< x w))
(assert (= x (str.++ "Z" xp)))
(assert (= w "A"))
(check-sat)"#;
    assert_eq!(verdict(s), CheckResult::Unsat);
}

#[test]
fn harness_surface_matches_front_door() {
    let s = r#"(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(declare-fun w () String)
(declare-fun xp () String)
(assert (str.<= x y))
(assert (str.<= y w))
(assert (= x (str.++ "G" xp)))
(assert (= w "E"))
(check-sat)"#;
    let mut script = parse_script(s).expect("parse");
    assert_eq!(
        lex_order_verdict(&mut script, &cfg()),
        Some(CheckResult::Unsat)
    );
}

#[test]
fn satisfiable_lex_not_refuted() {
    // x ≤ y with no forcing equalities is satisfiable — the lex route must never
    // report a (wrong) unsat. The bounded encoder decides it sat.
    let s = r"(set-logic QF_SLIA)
(declare-const x String)
(declare-const y String)
(assert (str.<= x y))
(check-sat)";
    assert!(
        matches!(verdict(s), CheckResult::Sat(_)),
        "satisfiable lex script must not be refuted"
    );
}
