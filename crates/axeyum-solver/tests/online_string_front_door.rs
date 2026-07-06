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

#[test]
fn front_door_str002_congruence_unsat() {
    // The exact `r1_QF_S_str002` census shape (T-B.7 slice 3, concat-congruence):
    //   (or (= xx (yy++"aa")) (= zz (yy++"aa")))
    //   ∧ (not (= (xx++"bb") (yy++"aa"++"bb"))) ∧ (not (= (zz++"bb") (yy++"aa"++"bb")))
    // Each disjunct forces `_ ++ "bb" ≈ yy ++ "aa" ++ "bb"` by congruence, clashing
    // with the matching disequality — every branch is unsat. Both `str.++` results
    // exceed the ADR-0029 bound, so this reaches the online route as a word skeleton.
    let s = r#"(set-logic QF_S)
(declare-fun xx () String)
(declare-fun yy () String)
(declare-fun zz () String)
(assert (or (= xx (str.++ yy "aa")) (= zz (str.++ yy "aa"))))
(assert (and (not (= (str.++ xx "bb") (str.++ yy "aa" "bb")))
             (not (= (str.++ zz "bb") (str.++ yy "aa" "bb")))))
(check-sat)"#;
    assert_eq!(verdict(s), CheckResult::Unsat);
}

// ---------- census-shape membership UNSAT through the text front door ----------
//
// Disjunctive / negated `str.in_re` shapes the one-shot membership route declines
// (its atoms sit under `or` / `not(and)`), decided by the online CDCL(T) route via
// per-variable regex intersection behind a re-checked emptiness certificate.

#[test]
fn front_door_re_mod_eq_disjunctive_membership_unsat() {
    // The exact `re-mod-eq` census shape: (or (= x y) (= x z)) forces x equal to a
    // variable whose language is disjoint from x's, so both branches intersect to
    // the empty language. x ∈ A(BAA)*, y,z ∈ AB(AAB)*A.
    let s = r#"(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(declare-fun z () String)
(assert (or (= x y)(= x z)))
(assert (str.in_re x (re.++ (str.to_re "A") (re.* (str.to_re "BAA")))))
(assert (str.in_re y (re.++ (str.to_re "AB") (re.* (str.to_re "AAB")) (str.to_re "A"))))
(assert (str.in_re z (re.++ (str.to_re "AB") (re.* (str.to_re "AAB")) (str.to_re "A"))))
(check-sat)"#;
    assert_eq!(verdict(s), CheckResult::Unsat);
}

#[test]
fn front_door_re_neg_unfold_negated_membership_unsat() {
    // The exact `re-neg-unfold-rev-a` shape: assert1 forces `x ∈ R1`; assert2 is
    // ¬(A ∧ (x ∈ R2)) with A already true, so it forces `x ∉ R2`. R1 ⊆ R2, so
    // R1 ∩ ∁R2 is empty — a negative-membership intersection conflict.
    let s = r#"(set-logic QF_S)
(declare-const x String)
(declare-const y String)
(assert (and (= y "foobar") (str.in_re x (re.++ (str.to_re "ab") (re.* re.allchar) (str.to_re "b") (re.* re.allchar) (str.to_re "b") (re.* re.allchar) (str.to_re "b")))))
(assert (not (and (= y "foobar") (str.in_re x (re.++ (str.to_re "a") (re.* re.allchar) (str.to_re "b") (re.* re.allchar) (str.to_re "b") (re.* re.allchar) (str.to_re "b"))))))
(check-sat)"#;
    assert_eq!(verdict(s), CheckResult::Unsat);
}

#[test]
fn front_door_disjunctive_pure_membership_all_branches_empty_unsat() {
    // A pure-membership disjunction (no equalities): every disjunct intersects an
    // over-arching positive membership to the empty language.
    //   x ∈ (ab)*  ∧  (x ∈ (abab)ac* ∨ x ∈ (ba)*)
    // (ab)* ∩ anything-starting-"aba…"→"ac" is empty, and (ab)* ∩ (ba)* = {ε} but
    // the left needs length ≥ 2, forced below.
    let s = r#"(set-logic QF_S)
(declare-const x String)
(assert (str.in_re x (re.+ (str.to_re "ab"))))
(assert (or (str.in_re x (re.++ (str.to_re "abab") (str.to_re "ac")))
            (str.in_re x (re.+ (str.to_re "ba")))))
(check-sat)"#;
    assert_eq!(verdict(s), CheckResult::Unsat);
}

#[test]
fn front_door_re_loop_cong_fallback_membership_unsat() {
    // Regression for the P0 wrong-sat (`instance1079-re-loop-cong`): a `re.loop` is
    // outside the bounded encoder, so the script takes the word-first parse fallback
    // (empty flat `assertions`); its real content is the membership skeleton. X is
    // pinned by a positive singleton membership to an 11-char string ending in "\n",
    // which IS in the negated loop-concat language, so the conjunction is unsat.
    // A naive `check_auto` on the empty flat view returns a vacuous `sat`; the front
    // door consults the online membership route and returns `unsat`.
    let s = "(set-logic QF_S)\n\
(declare-const X String)\n\
(assert (not (str.in_re X (re.++ ((_ re.loop 0 16) (re.union re.allchar (str.to_re \"\\u{0a}\"))) (str.to_re \"\\u{0a}\")))))\n\
(assert (str.in_re X (str.to_re \"//cdmax/Ui\\u{0a}\")))\n\
(check-sat)";
    assert_eq!(verdict(s), CheckResult::Unsat);
    // The fallback parse leaves the flat view empty but populates the membership
    // skeleton — the route the front door consults.
    let script = parse_script(s).expect("parse re-loop fallback");
    assert!(script.assertions.is_empty());
    assert!(!script.word_skeleton_memberships.is_empty());
}

// ---------- census-shape membership SAT through the text front door ----------

#[test]
fn front_door_disjunctive_membership_consistent_branch_sat() {
    // (x ∈ (ab)*) ∧ (x ∈ (ab)+ ∨ x ∈ (cd)+) — branch 1 holds; a witness "abab"
    // matches, replayed by the reference matcher.
    let s = r#"(set-logic QF_S)
(declare-const x String)
(assert (str.in_re x (re.* (str.to_re "ab"))))
(assert (or (str.in_re x (re.+ (str.to_re "ab"))) (str.in_re x (re.+ (str.to_re "cd")))))
(assert (< 1 (str.len x)))
(check-sat)"#;
    assert!(
        matches!(verdict(s), CheckResult::Sat(_)),
        "the consistent-branch membership disjunction must decide sat"
    );
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

// ---------- Phase D: constant-pattern extended functions as regex memberships ----------
//
// `str.prefixof`/`str.suffixof`/`str.contains` with a **constant pattern** and a
// **single-variable subject** are exact regex memberships (`P·Σ*` / `Σ*·S` /
// `Σ*·C·Σ*`) — polarity-symmetric, so sound under a `not`. The online route
// decides them via the same certified-emptiness / matcher-replay discipline.

#[test]
fn front_door_prefixof_membership_conflict_unsat() {
    // The `re.all` census file: x ∈ "abc"·Σ* ∧ ¬prefixof("abc", x). The negated
    // prefixof is x ∉ "abc"·Σ* — the same language, so the class is empty.
    let s = r#"(set-logic QF_SLIA)
(declare-const x String)
(assert (str.in_re x (re.++ (str.to_re "abc") re.all)))
(assert (not (str.prefixof "abc" x)))
(check-sat)"#;
    assert_eq!(verdict(s), CheckResult::Unsat);
}

#[test]
fn front_door_contains_and_negated_contains_unsat() {
    // contains(x,"a") ∧ ¬contains(x,"a") — x ∈ Σ*·a·Σ* ∧ x ∉ Σ*·a·Σ*, empty class.
    let s = r#"(set-logic QF_S)
(declare-const x String)
(assert (str.contains x "a"))
(assert (not (str.contains x "a")))
(check-sat)"#;
    assert_eq!(verdict(s), CheckResult::Unsat);
}

#[test]
fn front_door_suffixof_membership_sat_replays() {
    // ¬suffixof("a", x) ∧ contains(x, "b") is SAT (e.g. x = "b"); the model must
    // replay against the original extended-function atoms.
    let s = r#"(set-logic QF_S)
(declare-const x String)
(assert (not (str.suffixof "a" x)))
(assert (str.contains x "b"))
(check-sat)"#;
    match verdict(s) {
        CheckResult::Sat(_) => {}
        other => panic!("expected SAT for a satisfiable suffix/contains problem, got {other:?}"),
    }
}

#[test]
fn front_door_never_wrong_unsat_on_sat_contains() {
    // contains(x,"a") ∧ contains(x,"b") is SAT (x = "ab"); never unsat.
    let s = r#"(set-logic QF_S)
(declare-const x String)
(assert (str.contains x "a"))
(assert (str.contains x "b"))
(check-sat)"#;
    if let CheckResult::Unsat = verdict(s) {
        panic!("WRONG UNSAT on a satisfiable contains conjunction — a soundness bug");
    }
}

// ---------- Phase D: constant-fold str.replace (constant haystack + needle) ----------

#[test]
fn front_door_constant_replace_identity_unsat() {
    // The `replace-find-base` census file: replace("ABCDEF","C",x) is exactly
    // "AB"++x++"DEF", so the negated equality is unsatisfiable.
    let s = r#"(set-logic QF_SLIA)
(declare-fun x () String)
(assert (not (= (str.replace "ABCDEF" "C" x) (str.++ "AB" x "DEF"))))
(check-sat)"#;
    assert_eq!(verdict(s), CheckResult::Unsat);
}

#[test]
fn front_door_constant_replace_empty_needle_unsat() {
    // Empty needle: replace("abc","",x) = x ++ "abc" (first occurrence at index 0).
    let s = r#"(set-logic QF_SLIA)
(declare-fun x () String)
(assert (not (= (str.replace "abc" "" x) (str.++ x "abc"))))
(check-sat)"#;
    assert_eq!(verdict(s), CheckResult::Unsat);
}

#[test]
fn front_door_constant_replace_absent_needle_unsat() {
    // Needle absent: replace("abc","z",x) = "abc" (unchanged, x irrelevant).
    let s = r#"(set-logic QF_SLIA)
(declare-fun x () String)
(assert (not (= (str.replace "abc" "z" x) "abc")))
(check-sat)"#;
    assert_eq!(verdict(s), CheckResult::Unsat);
}

#[test]
fn front_door_constant_replace_sat_replays() {
    // replace("ABCDEF","C",x) = "ABzDEF" pins x = "z"; SAT with a replaying model.
    let s = r#"(set-logic QF_SLIA)
(declare-fun x () String)
(assert (= (str.replace "ABCDEF" "C" x) "ABzDEF"))
(check-sat)"#;
    match verdict(s) {
        CheckResult::Sat(_) => {}
        other => panic!("expected SAT pinning x = \"z\", got {other:?}"),
    }
}
