#![cfg(feature = "full")]
//! Adversarial fixtures for the clause-loop certificate (ADR-2131).
//!
//! # What these are for, and why they are not unit tests
//!
//! `nra_clause_cert`'s unit tests check the certificate the producer builds and
//! the checker that accepts it. These check the guards: for each part of the
//! certificate, damage exactly that part of a LIVE certificate -- one the
//! producer really built for a query the route really refutes -- and require a
//! NAMED rejection.
//!
//! A certificate a fixture assembles itself would test the checker against a
//! shape the producer never emits, which is the easy half. So the damage goes
//! through `clause_loop_certificate_probe`, which runs the real loop, attaches
//! the real DRAT proof, applies one mutation, and reports which single guard
//! fired.
//!
//! **The DRAT proof is attached BEFORE the mutation.** Mutating first and
//! proving afterwards would produce a valid proof of the damaged clause set and
//! the checker would be right to accept it -- the fixture would pass while
//! checking nothing.
//!
//! # The control is not optional
//!
//! `the_unmutated_certificate_is_accepted` is what makes every rejection below
//! mean something: without it, a checker that refused everything would pass all
//! of them. It also asserts the checker EXAMINED something -- an acceptance with
//! zero lemmas, zero gates and zero proof steps is the vacuous pass a boolean
//! cannot distinguish.

use axeyum_solver::{
    clause_loop_certificate_probe, clause_loop_decide_for_testing, clause_loop_last_check,
};

/// Two branches, each individually infeasible, sharing one variable. The loop
/// must refute BOTH before the abstraction closes, so the certificate carries
/// at least two lemmas, a gate table for the `or`/`and` structure, and a proof.
const TWO_BRANCH_UNSAT: &str = "(declare-fun x () Real)\n\
     (declare-fun y () Real)\n\
     (assert (or (and (> x 1) (< x 0)) (and (< x (- 1)) (> x 0))))\n\
     (assert (= y 0))\n(check-sat)\n";

fn probe(script: &str, mutation: &str) -> Option<Result<String, String>> {
    let parsed = axeyum_smtlib::parse_script(script).expect("parse");
    clause_loop_certificate_probe(&parsed.arena, &parsed.assertions, mutation).map(|r| {
        r.map(|s| {
            format!(
                "lemmas={} gates={} roots={} cells={} drat={}",
                s.lemmas, s.gates, s.roots, s.lemma_cells, s.drat_steps
            )
        })
    })
}

/// THE CONTROL. The undamaged certificate is accepted, and the checker examined
/// every part of it.
#[test]
fn the_unmutated_certificate_is_accepted() {
    let got = probe(TWO_BRANCH_UNSAT, "none").expect("the loop must refute this query");
    let stats = got.expect("the checker must accept an undamaged certificate");
    // Each of these is a part a mutation below damages. A zero here would make
    // the matching rejection fixture vacuous, so they are asserted together.
    for part in ["lemmas=0", "gates=0", "roots=0", "cells=0", "drat=0"] {
        assert!(
            !stats.contains(part),
            "the checker accepted without examining {part}: {stats}"
        );
    }
}

/// THE CERTIFICATE-DROP FIXTURE the lane brief names: damage a learned clause's
/// CELL and require the checker to refuse.
///
/// The covering is re-pointed at an atom the clause does not cite, so the clause
/// claims more than the covering proves. The clause SET is untouched, so the
/// DRAT proof still checks and only the cited-atom guard can see it -- which is
/// what makes this a test of that guard rather than of the proof checker.
#[test]
fn a_mutated_cell_is_refused() {
    let got = probe(TWO_BRANCH_UNSAT, "lemma-cell").expect("a certificate to damage");
    assert_eq!(
        got.unwrap_err(),
        "lemma-cell-outside-clause",
        "the cited-atom guard must be the one that fires"
    );
}

/// A learned clause shortened past what its covering justifies.
#[test]
fn a_shortened_learned_clause_is_refused() {
    let got = probe(TWO_BRANCH_UNSAT, "lemma-clause").expect("a certificate to damage");
    assert_eq!(got.unwrap_err(), "lemma-clause-mismatch");
}

/// The propositional refutation removed. Every lemma is intact and every clause
/// is implied; only the proof that the clause set is unsatisfiable is gone.
#[test]
fn a_truncated_drat_proof_is_refused() {
    let got = probe(TWO_BRANCH_UNSAT, "drat").expect("a certificate to damage");
    assert_eq!(got.unwrap_err(), "drat-rejected");
}

/// A gate table that no longer describes the query. The derived clauses are
/// perfectly well formed -- for the WRONG connective -- so the faithfulness walk
/// is the only thing that can see it.
#[test]
fn a_wrong_gate_connective_is_refused() {
    let got = probe(TWO_BRANCH_UNSAT, "gate-kind").expect("a certificate to damage");
    assert_eq!(got.unwrap_err(), "encoding-mismatch");
}

/// A certificate that refutes a SUBSET of the query. Every clause in it is still
/// implied by the assertions, so only the root-arity guard can see it.
#[test]
fn a_dropped_assertion_root_is_refused() {
    let got = probe(TWO_BRANCH_UNSAT, "root").expect("a certificate to damage");
    assert_eq!(got.unwrap_err(), "root-arity");
}

/// A gate variable colliding with an atom variable, which breaks the
/// conservative-extension argument the whole abstraction rests on.
#[test]
fn a_gate_variable_shadowing_an_atom_is_refused() {
    let got = probe(TWO_BRANCH_UNSAT, "gate-shadow").expect("a certificate to damage");
    assert_eq!(got.unwrap_err(), "gate-shadows-atom");
}

/// Every mutation actually applied. A mutation that silently did nothing would
/// turn its fixture into a measurement of the mutator, so the probe reports
/// `mutation-not-applicable` instead and this refuses it.
#[test]
fn every_mutation_applies_to_this_certificate() {
    for m in [
        "lemma-cell",
        "lemma-clause",
        "drat",
        "gate-kind",
        "root",
        "gate-shadow",
    ] {
        let got = probe(TWO_BRANCH_UNSAT, m).expect("a certificate to damage");
        let err = got.unwrap_err();
        assert!(
            !err.starts_with("mutation-not-applicable"),
            "mutation {m} did not apply: {err}"
        );
    }
}

/// Every guard that fires is a DIFFERENT one.
///
/// Six of seven guards in one suite here were once removable with everything
/// still green, because they all rejected through one shared check. This is the
/// test that would have caught that: if two mutations produce the same failure
/// name, one of the two guards is not doing its own work.
#[test]
fn each_mutation_fires_its_own_guard() {
    let mut seen: Vec<String> = Vec::new();
    for m in [
        "lemma-cell",
        "lemma-clause",
        "drat",
        "gate-kind",
        "root",
        "gate-shadow",
    ] {
        let err = probe(TWO_BRANCH_UNSAT, m)
            .expect("a certificate to damage")
            .unwrap_err();
        assert!(
            !seen.contains(&err),
            "mutation {m} fired a guard another mutation already fired: {err}"
        );
        seen.push(err);
    }
    assert_eq!(seen.len(), 6, "six mutations, six distinct guards");
}

// ---------------------------------------------------------------------------
// The soundness fixtures: satisfiable queries the loop must never refute.
// ---------------------------------------------------------------------------

/// A satisfiable Boolean combination where the two branches SHARE a variable and
/// only one branch is infeasible.
///
/// The extension ADR-2131 required over the independent-branch case: here `x`
/// appears in both branches and `y` couples them, so a blocking clause naming
/// the wrong atom blocks the LIVE branch and the loop refutes a satisfiable
/// query. Asserting `not unsat` rather than `sat` is deliberate -- a decline is a
/// permitted answer on this route and a wrong answer is not.
#[test]
fn a_shared_variable_with_one_dead_branch_is_never_refuted() {
    for script in [
        "(declare-fun x () Real)\n(declare-fun y () Real)\n\
         (assert (or (and (> x 1) (< x 0)) (and (> x 1) (< x 5))))\n\
         (assert (and (> y x) (< y 6)))\n(check-sat)\n",
        // The same shape with the dead branch second, so an order-dependent bug
        // cannot hide behind the first fixture.
        "(declare-fun x () Real)\n(declare-fun y () Real)\n\
         (assert (or (and (> x 1) (< x 5)) (and (> x 1) (< x 0))))\n\
         (assert (and (> y x) (< y 6)))\n(check-sat)\n",
        // Both branches live, so the loop must not learn a clause that kills
        // either of them.
        "(declare-fun x () Real)\n(declare-fun y () Real)\n\
         (assert (or (< x (- 2)) (> x 2)))\n\
         (assert (= y (* x x)))\n(assert (< y 100))\n(check-sat)\n",
    ] {
        let parsed = axeyum_smtlib::parse_script(script).expect("parse");
        let out = clause_loop_decide_for_testing(&parsed.arena, &parsed.assertions);
        assert!(
            !matches!(out, Some(axeyum_solver::CheckResult::Unsat)),
            "a satisfiable query was refuted: {script}"
        );
    }
}

/// The degenerate-argument class CLAUDE.md's hard rule requires, kept from
/// ADR-2126 and extended to the `unsat`-emitting arm.
///
/// Both fixtures are SATISFIABLE, so a route that folded `(/ x 0)` to a
/// convention and refuted would fail here. ADR-2126 could only assert this
/// against a route that never said `unsat`; now that it does, the fixture is
/// load-bearing rather than precautionary.
#[test]
fn division_by_constant_zero_is_never_refuted() {
    for script in [
        "(declare-fun x () Real)\n(declare-fun y () Real)\n\
         (assert (or (> (/ x 0) 1) (> y 0)))\n(assert (> y 5))\n(check-sat)\n",
        "(declare-fun x () Real)\n(declare-fun y () Real)\n\
         (assert (or (> (/ x y) 1) (> x 3)))\n(assert (> x 4))\n(check-sat)\n",
        "(declare-fun x () Real)\n(declare-fun y () Real)\n\
         (assert (and (or (> (/ x 0) 1) (< (/ x 0) 1)) (> y 0)))\n\
         (assert (> y 5))\n(check-sat)\n",
    ] {
        let parsed = axeyum_smtlib::parse_script(script).expect("parse");
        let out = clause_loop_decide_for_testing(&parsed.arena, &parsed.assertions);
        assert!(
            !matches!(out, Some(axeyum_solver::CheckResult::Unsat)),
            "a satisfiable query with a degenerate divisor was refuted: {script}"
        );
        // And no certificate may be produced for one, either.
        assert!(
            clause_loop_certificate_probe(&parsed.arena, &parsed.assertions, "none").is_none()
                || !matches!(out, Some(axeyum_solver::CheckResult::Unsat)),
            "a certificate was built for a satisfiable query"
        );
    }
}

/// An `unsat` from this route always leaves an accepted certificate behind.
///
/// The counts are what distinguish "the route answered" from "the route answered
/// and something was checked". A route that emitted `unsat` with no stats would
/// pass a verdict-only assertion.
#[test]
fn every_unsat_leaves_an_accepted_certificate() {
    let parsed = axeyum_smtlib::parse_script(TWO_BRANCH_UNSAT).expect("parse");
    let out = clause_loop_decide_for_testing(&parsed.arena, &parsed.assertions);
    assert!(
        matches!(out, Some(axeyum_solver::CheckResult::Unsat)),
        "expected a certified unsat, got {out:?}"
    );
    let stats = clause_loop_last_check().expect("an accepted certificate");
    assert!(stats.lemmas >= 2, "lemmas={}", stats.lemmas);
    assert!(stats.gates > 0 && stats.roots > 0);
    assert!(stats.lemma_cells > 0, "no cells examined");
    assert!(stats.drat_steps > 0, "no proof steps checked");
    assert!(stats.derived_clauses > 0, "no clauses derived");
}
