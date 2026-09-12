//! A `define-sort` alias used as a QUANTIFIER BINDER sort, end to end.
//!
//! The SMT-LIB front door parsed binder sorts against an **empty** alias map:
//! `sort_aliases` were threaded into every declaration-site `parse_sort` call
//! but never into term conversion. So `(define-sort MyInt () Int)` followed by
//! `(exists ((y MyInt)) …)` died at PARSE with `unsupported: sort "MyInt"`,
//! while the very same alias on a `declare-fun` worked. The whole SMT-LIB `FP`
//! division is written that way, so none of it reached the solver at all.
//!
//! These tests assert VERDICTS, not just that a parse succeeds: each aliased
//! script is decided, and decided identically to the same script with the alias
//! spelled out. Comparing the two alone would pass vacuously if both came back
//! `Unknown`, so the expected verdict is named explicitly as well.
#![cfg(feature = "full")]

use std::time::Duration;

use axeyum_smtlib::parse_script;
use axeyum_solver::{CheckResult, SolverConfig, solve};

fn config() -> SolverConfig {
    SolverConfig::new().with_timeout(Duration::from_secs(20))
}

/// Parses `text` and decides its assertions, naming the verdict `sat`/`unsat`/
/// `unknown`.
fn verdict(text: &str) -> &'static str {
    let mut script = parse_script(text).expect("script parses");
    match solve(&mut script.arena, &script.assertions, &config()).expect("query decides") {
        CheckResult::Sat(_) => "sat",
        CheckResult::Unsat => "unsat",
        CheckResult::Unknown(_) => "unknown",
    }
}

/// The aliased script and the spelled-out script must reach the same, DECIDED
/// verdict, and that verdict must be `expected`.
fn assert_alias_agrees(aliased: &str, spelled: &str, expected: &str) {
    let spelled_verdict = verdict(spelled);
    assert_eq!(
        spelled_verdict, expected,
        "the alias-free control must be {expected}; it was {spelled_verdict}. \
         The control is the authority here — if it moved, this test is measuring \
         the wrong thing, not the alias."
    );
    let aliased_verdict = verdict(aliased);
    assert_eq!(
        aliased_verdict, expected,
        "an aliased binder sort must decide exactly as the spelled-out sort does"
    );
}

#[test]
fn exists_over_int_alias_is_sat() {
    assert_alias_agrees(
        "(set-logic LIA)\n\
         (define-sort MyInt () Int)\n\
         (assert (exists ((y MyInt)) (= y 3)))\n\
         (check-sat)\n",
        "(set-logic LIA)\n\
         (assert (exists ((y Int)) (= y 3)))\n\
         (check-sat)\n",
        "sat",
    );
}

#[test]
fn forall_over_int_alias_is_unsat() {
    // ∀y:Int. y = 3 is false, so the assertion is unsatisfiable. This is the
    // direction that matters for soundness: the fix must not turn a refutable
    // script into a satisfiable one by mis-sorting the binder.
    assert_alias_agrees(
        "(set-logic LIA)\n\
         (define-sort MyInt () Int)\n\
         (assert (forall ((y MyInt)) (= y 3)))\n\
         (check-sat)\n",
        "(set-logic LIA)\n\
         (assert (forall ((y Int)) (= y 3)))\n\
         (check-sat)\n",
        "unsat",
    );
}

#[test]
fn exists_over_bitvec_alias_is_sat() {
    assert_alias_agrees(
        "(set-logic BV)\n\
         (define-sort Byte () (_ BitVec 8))\n\
         (declare-fun x () Byte)\n\
         (assert (exists ((y Byte)) (= (bvadd x y) #x00)))\n\
         (check-sat)\n",
        "(set-logic BV)\n\
         (declare-fun x () (_ BitVec 8))\n\
         (assert (exists ((y (_ BitVec 8))) (= (bvadd x y) #x00)))\n\
         (check-sat)\n",
        "sat",
    );
}

#[test]
fn forall_over_bitvec_alias_is_unsat() {
    // ∀y:(_ BitVec 8). y = #x00 is false (y = #x01 refutes it).
    assert_alias_agrees(
        "(set-logic BV)\n\
         (define-sort Byte () (_ BitVec 8))\n\
         (assert (forall ((y Byte)) (= y #x00)))\n\
         (check-sat)\n",
        "(set-logic BV)\n\
         (assert (forall ((y (_ BitVec 8))) (= y #x00)))\n\
         (check-sat)\n",
        "unsat",
    );
}

#[test]
fn as_const_over_array_alias_is_sat() {
    // `(as const S)` is the other term-conversion sort position that was parsed
    // against an empty alias map.
    //
    // THE SHAPE MATTERS, and the obvious one is VACUOUS. `(select ((as const A) v) i)`
    // is rewritten by `reduce_const_array_sexpr` at the S-EXPRESSION level, before
    // any sort is parsed, so it parses either way and pins nothing — confirmed by
    // running the pre-fix binary on it. `distinct` is not one of the reduced heads,
    // so this shape does reach `apply_parameterized`, where the sort is parsed.
    //
    // `a` is a free array, so it can differ from the all-zero constant array: sat.
    assert_alias_agrees(
        "(set-logic QF_ABV)\n\
         (define-sort BA () (Array (_ BitVec 4) (_ BitVec 8)))\n\
         (declare-const a BA)\n\
         (assert (distinct a ((as const BA) #x00)))\n\
         (check-sat)\n",
        "(set-logic QF_ABV)\n\
         (declare-const a (Array (_ BitVec 4) (_ BitVec 8)))\n\
         (assert (distinct a ((as const (Array (_ BitVec 4) (_ BitVec 8))) #x00)))\n\
         (check-sat)\n",
        "sat",
    );
}
