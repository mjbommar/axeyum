//! One invariant, across evidence kinds: **claiming certification means
//! surviving an independent re-check.**
//!
//! `Evidence::is_certified` is a static property of the variant — a promise that
//! this kind of evidence carries a checkable object. `Evidence::check_outcome`
//! is the run that redeems the promise. Nothing tied the two together, and the
//! per-variant suites cannot: each one exercises the variant its author added,
//! so a new variant arrives with no general obligation to meet.
//!
//! # The failure this exists to prevent, measured
//!
//! On 2026-08-17 a new `Evidence::UnsatQuantInstanceSet` was added, wired into
//! `is_certified`, and shipped. It reported:
//!
//! ```text
//! one instance     kind=unsat-quant-instance-set certified=1 arena=ok
//! two instances    kind=unsat-quant-instance-set certified=1 arena=FAIL
//! four instances   kind=unsat-quant-instance-set certified=1 arena=FAIL
//! ```
//!
//! `certified=1` on evidence whose independent re-check FAILED — and `FAIL` is
//! the soundness-alarm state, meaning producer and checker disagree. The single
//! instance "passed" only because the checker happened to rebuild its term at
//! the same `TermId`.
//!
//! The cause is architectural, not a typo. That certificate carries `TermId`s
//! naming terms created *during* solving, and `smtcomp_cli` re-validates against
//! a **fresh parse of the original file** — deliberately, so re-validation is
//! independent of anything the producing run kept in memory. Ids from one arena
//! mean nothing in another. It was reverted; this test is what should have
//! caught it.
//!
//! # Why re-parsing is the whole point
//!
//! Checking against the producer's own arena would pass for any certificate,
//! including one that is simply a copy of the producer's conclusions. Parsing
//! the text again builds an arena that shares no state with the solve, so a
//! certificate survives only if it says something about the *query* rather than
//! about that run.

#![cfg(feature = "full")]

use axeyum_smtlib::parse_script;
use axeyum_solver::{EvidenceCheck, SolverConfig, produce_evidence};

/// `(name, smtlib2)`. Each must be `unsat`; a `sat` or `unknown` query would
/// make the invariant vacuous for that row.
const QUERIES: &[(&str, &str)] = &[
    (
        "qf_bv_comparison",
        "(set-logic QF_BV)\n\
         (declare-fun a () (_ BitVec 4))\n\
         (declare-fun b () (_ BitVec 4))\n\
         (assert (bvule a b))\n\
         (assert (bvult b a))\n\
         (check-sat)",
    ),
    (
        "qf_lia_contradiction",
        "(set-logic QF_LIA)\n\
         (declare-fun x () Int)\n\
         (assert (> x 5))\n\
         (assert (< x 3))\n\
         (check-sat)",
    ),
    (
        "bool_contradiction",
        "(set-logic QF_UF)\n\
         (declare-fun p () Bool)\n\
         (assert p)\n\
         (assert (not p))\n\
         (check-sat)",
    ),
    // The shapes that exposed the defect: a universal refuted by instantiating
    // it at ground terms, at ONE instance and at several. One instance is not
    // enough — that is the case that accidentally passed.
    (
        "quantified_one_instance",
        "(set-logic UFLIA)\n\
         (declare-fun f (Int) Int)\n\
         (assert (forall ((x Int)) (= (f x) 0)))\n\
         (assert (not (= (f 5) 0)))\n\
         (check-sat)",
    ),
    (
        "quantified_two_instances",
        "(set-logic UFLIA)\n\
         (declare-fun f (Int) Int)\n\
         (assert (forall ((x Int)) (= (f x) 0)))\n\
         (assert (not (= (+ (f 5) (f 7)) 0)))\n\
         (check-sat)",
    ),
    (
        "quantified_four_instances",
        "(set-logic UFLIA)\n\
         (declare-fun f (Int) Int)\n\
         (declare-fun g (Int) Int)\n\
         (assert (forall ((x Int)) (= (f x) 0)))\n\
         (assert (forall ((y Int)) (= (g y) 1)))\n\
         (assert (not (= (+ (f 5) (f 7) (g 9) (g 11)) 2)))\n\
         (check-sat)",
    ),
    // QF_NIA single-variable polynomial equalities. Added with the certificate
    // itself: this suite is the general obligation a new variant must meet, and
    // meeting it only inside the variant's own suite is how
    // `UnsatQuantInstanceSet` shipped `certified=1` over a FAILED re-check.
    // All three carry `TermId`-free certificates, which is exactly what the
    // fresh-parse re-validation below is able to distinguish.
    (
        "nia_non_square_discriminant",
        "(set-logic QF_NIA)\n\
         (declare-fun x () Int)\n\
         (assert (= (+ (* x x) x (- 1)) 0))\n\
         (check-sat)",
    ),
    (
        "nia_non_integral_rational_roots",
        "(set-logic QF_NIA)\n\
         (declare-fun x () Int)\n\
         (assert (= (+ (* 4 x x) (- 1)) 0))\n\
         (check-sat)",
    ),
    (
        "nia_rational_root_exhausted",
        "(set-logic QF_NIA)\n\
         (declare-fun x () Int)\n\
         (assert (= (+ (* x x x) x 1) 0))\n\
         (check-sat)",
    ),
    // QF_NRA monomial divisibility. Unlike the QF_NIA rows above, these two
    // shapes are taken verbatim from committed corpus files
    // (`cli__regress1__nl__zero-subset`, `cli__regress0__nl__subs0-unsat-confirm`),
    // which shipped as bare `Evidence::Unsat(None)` until 2026-08-20.
    (
        "nra_zero_product_divides",
        "(set-logic QF_NRA)\n\
         (declare-fun a () Real)(declare-fun b () Real)(declare-fun c () Real)\n\
         (declare-fun d () Real)(declare-fun e () Real)\n\
         (assert (= (* a b c d) 0))\n\
         (assert (not (= (* a b c d e) 0)))\n\
         (check-sat)",
    ),
    (
        "nra_zero_product_case_split",
        "(set-logic QF_NRA)\n\
         (declare-fun v1 () Real)(declare-fun v2 () Real)(declare-fun v3 () Real)\n\
         (declare-fun v4 () Real)(declare-fun v5 () Real)\n\
         (assert (or (= v1 0) (= v2 0)))\n\
         (assert (not (= (* v1 v2 v3 v4 v5) 0)))\n\
         (check-sat)",
    ),
    (
        "skolemised_existential",
        "(set-logic UF)\n\
         (declare-sort Person 0)\n\
         (declare-fun shaves (Person Person) Bool)\n\
         (assert (exists ((b Person)) \
            (forall ((x Person)) (= (shaves b x) (not (shaves x x))))))\n\
         (check-sat)",
    ),
];

struct Row {
    name: &'static str,
    kind: &'static str,
    certified: bool,
    outcome: EvidenceCheck,
}

fn measure() -> Vec<Row> {
    let config = SolverConfig::default();
    QUERIES
        .iter()
        .map(|(name, text)| {
            // Produce on one arena...
            let mut produced = parse_script(text).expect("query parses");
            let assertions = produced.assertions.clone();
            let report = produce_evidence(&mut produced.arena, &assertions, &config)
                .expect("evidence production runs");

            // ...and re-validate on an arena that shares nothing with it.
            let fresh = parse_script(text).expect("query re-parses");
            let outcome = report
                .evidence
                .check_outcome(&fresh.arena, &fresh.assertions)
                .expect("the checker must not error");

            Row {
                name,
                kind: report.evidence.kind_label(),
                certified: report.evidence.is_certified(),
                outcome,
            }
        })
        .collect()
}

/// The invariant.
#[test]
fn certified_evidence_survives_an_independent_reparse() {
    let rows = measure();
    let mut violations = Vec::new();
    for row in &rows {
        println!(
            "  {:<28} kind={:<32} certified={} outcome={}",
            row.name,
            row.kind,
            u8::from(row.certified),
            row.outcome.label()
        );
        if row.certified && !row.outcome.is_verified() {
            violations.push(format!(
                "{}: kind={} claims certification but re-validating against a FRESH PARSE \
                 returned {}. Either the certificate does not describe the query (it may name \
                 terms that exist only in the producing run's arena), or the checker is wrong. \
                 Both are defects; neither may ship as `certified`",
                row.name,
                row.kind,
                row.outcome.label()
            ));
        }
    }
    assert!(violations.is_empty(), "{}", violations.join("\n"));
}

/// The invariant above is satisfiable by evidence that never claims anything, so
/// this requires the corpus to actually exercise the `certified` branch.
///
/// Without it, deleting `is_certified` entirely — or having every route decline
/// to certify — would leave the test above green while proving nothing.
#[test]
fn the_corpus_actually_exercises_certified_evidence() {
    let rows = measure();
    let certified: Vec<&str> = rows
        .iter()
        .filter(|row| row.certified)
        .map(|row| row.name)
        .collect();
    assert!(
        certified.len() >= 3,
        "only {} of {} rows produced certified evidence ({certified:?}); the invariant test \
         is then close to vacuous. Add queries whose routes certify, or find out why these \
         stopped",
        certified.len(),
        rows.len()
    );
    let verified = rows.iter().filter(|row| row.outcome.is_verified()).count();
    assert!(
        verified >= 3,
        "only {verified} rows re-validated against a fresh parse; this test cannot \
         distinguish a working checker from one that never runs"
    );
}
