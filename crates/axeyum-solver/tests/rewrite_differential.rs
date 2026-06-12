//! Oracle differential checks for the default rewrite canonicalizer.
//!
//! These tests keep the rewrite crate free of a normal Z3 dependency while
//! still requiring enabled default rules to preserve solver behavior and model
//! replay through the existing oracle path.

#![cfg(feature = "z3")]

use axeyum_ir::{TermArena, TermId, Value, eval};
use axeyum_rewrite::canonicalize_terms;
use axeyum_solver::{CheckResult, Model, SolverBackend, SolverConfig, Z3Backend};

fn check(arena: &TermArena, assertions: &[TermId]) -> CheckResult {
    Z3Backend::new()
        .check(arena, assertions, &SolverConfig::default())
        .expect("backend invocation succeeds")
}

fn assert_rewrite_oracle_equivalent(
    arena: &mut TermArena,
    assertions: &[TermId],
    label: &str,
    require_change: bool,
) {
    let original = check(arena, assertions);
    let rewritten = canonicalize_terms(arena, assertions).expect("canonicalization succeeds");
    if require_change {
        assert!(
            rewritten.changed(),
            "{label}: fixture should exercise at least one rewrite rule"
        );
    }
    let rewritten_result = check(arena, &rewritten.terms);

    match (&original, &rewritten_result) {
        (CheckResult::Sat(original_model), CheckResult::Sat(rewritten_model)) => {
            replay(arena, assertions, original_model, label);
            replay(arena, assertions, rewritten_model, label);
            replay(arena, &rewritten.terms, original_model, label);
            replay(arena, &rewritten.terms, rewritten_model, label);
        }
        (CheckResult::Unsat, CheckResult::Unsat) => {}
        _ => panic!(
            "{label}: rewrite changed oracle decision: original={original:?} rewritten={rewritten_result:?}"
        ),
    }
}

fn replay(arena: &TermArena, assertions: &[TermId], model: &Model, label: &str) {
    let assignment = model.to_assignment();
    for &assertion in assertions {
        assert_eq!(
            eval(arena, assertion, &assignment).unwrap(),
            Value::Bool(true),
            "{label}: model replay failed for assertion #{}",
            assertion.index()
        );
    }
}

#[test]
fn handcrafted_sat_and_unsat_queries_match_after_rewrite() {
    let mut sat = TermArena::new();
    let x = sat.bv_var("x", 8).unwrap();
    let p = sat.bool_var("p").unwrap();
    let zero = sat.bv_const(8, 0).unwrap();
    let five = sat.bv_const(8, 5).unwrap();
    let x_plus_zero = sat.bv_add(x, zero).unwrap();
    let x_is_five = sat.eq(x_plus_zero, five).unwrap();
    let p_implies_p = sat.implies(p, p).unwrap();
    assert_rewrite_oracle_equivalent(&mut sat, &[x_is_five, p_implies_p], "sat identities", true);

    let mut unsat = TermArena::new();
    let y = unsat.bv_var("y", 8).unwrap();
    let zero = unsat.bv_const(8, 0).unwrap();
    let y_plus_zero = unsat.bv_add(y, zero).unwrap();
    let below_zero = unsat.bv_ult(y_plus_zero, zero).unwrap();
    assert_rewrite_oracle_equivalent(&mut unsat, &[below_zero], "unsat identities", true);
}

#[test]
fn micro_corpus_matches_after_rewrite() {
    for (label, text) in [
        (
            "sat-add",
            include_str!("../../../corpus/micro/sat-add.smt2"),
        ),
        (
            "sat-quoted-symbol",
            include_str!("../../../corpus/micro/sat-quoted-symbol.smt2"),
        ),
        (
            "unsat-ult-zero",
            include_str!("../../../corpus/micro/unsat-ult-zero.smt2"),
        ),
    ] {
        let mut script = axeyum_smtlib::parse_script(text).expect("micro corpus parses");
        assert_rewrite_oracle_equivalent(&mut script.arena, &script.assertions, label, false);
    }
}
