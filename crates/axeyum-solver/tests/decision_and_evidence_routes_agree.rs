//! **The decision route and the evidence route must agree on the same query.**
//!
//! `solve` answers the verdict; `produce_evidence` answers it *with an
//! artifact*. They are separate code paths, and nothing in this tree compared
//! them — so when one regressed, the only way to notice was to point
//! `diagnose_evidence` at a file by hand.
//!
//! # Two instances of exactly that, both found on 2026-08-20, neither by a test
//!
//! `cli__regress0__nl__issue3003.smt2`: `check_auto_explained` answered `sat` in
//! 0.87 ms while `produce_evidence` answered `unknown`. The cause was three
//! layers down — `RealAlgebraic` addition declined whenever a rational operand's
//! isolating interval collapsed onto its own root, which happens on the FIRST
//! refinement of every rational, so the model replay guard rejected a correct
//! model. The decision route does not replay; the evidence route does. Fixed in
//! `crates/axeyum-ir/src/poly_big.rs`.
//!
//! `r0_QF_SLIA_replace-find-base.smt2`: a committed dominance audit recorded
//! `unsat`, and building that audit's own commit answered `sat` — a wrong
//! answer, since fixed. Nothing re-ran it for two months.
//!
//! # What this asserts
//!
//! If `solve` decides (`Sat` or `Unsat`), `produce_evidence` must not answer
//! `Unknown`, and must not answer the OPPOSITE verdict. A decided query whose
//! evidence route gives up is a capability the artifact pipeline has silently
//! lost; opposite verdicts would be a soundness alarm.
//!
//! It deliberately does NOT require evidence to be `certified`. Plenty of
//! fragments legitimately return a bare `unsat` today, and demanding a
//! certificate here would make this a coverage ratchet rather than an agreement
//! check — two different properties, and conflating them is how a gate starts
//! failing for reasons nobody wants to fix.

#![cfg(feature = "full")]

use axeyum_smtlib::parse_script;
use axeyum_solver::{CheckResult, Evidence, SolverConfig, produce_evidence, solve};

/// `(name, smtlib2)`. Chosen to spread across the fragments whose evidence
/// routes are separate implementations, so a regression in any one of them
/// shows up here rather than in a hand-run diagnostic.
const QUERIES: &[(&str, &str)] = &[
    // The regression this file exists for: a `sat` whose model needs algebraic
    // arithmetic to replay. Reduced from `cli__regress0__nl__issue3003.smt2`.
    (
        "nra_algebraic_model_replay",
        "(set-logic QF_NRA)\n\
         (declare-fun x () Real)\n(declare-fun y () Real)\n\
         (assert (>= x 0))\n\
         (assert (= (* x x) (+ 1 (* y (* y (- 1))))))\n\
         (check-sat)",
    ),
    // The four QF_NRA certificate shapes landed today.
    (
        "nra_zero_product",
        "(set-logic QF_NRA)\n\
         (declare-fun a () Real)(declare-fun b () Real)(declare-fun c () Real)\n\
         (declare-fun d () Real)(declare-fun e () Real)\n\
         (assert (= (* a b c d) 0))\n(assert (not (= (* a b c d e) 0)))\n(check-sat)",
    ),
    (
        "nra_product_positivstellensatz",
        "(set-logic QF_NRA)\n\
         (declare-fun x () Real)(declare-fun y () Real)(declare-fun z () Real)\n\
         (assert (> z 0))(assert (> x y))(assert (< (* x z) (* y z)))\n(check-sat)",
    ),
    (
        "nra_monomial_bound",
        "(set-logic QF_NRA)\n\
         (declare-fun a () Real)(declare-fun b () Real)\n\
         (declare-fun c () Real)(declare-fun d () Real)\n\
         (assert (>= a 1))(assert (>= b 1))(assert (>= c 1))(assert (>= d 1))\n\
         (assert (< (* a b c d) 1))\n(check-sat)",
    ),
    (
        "nia_univariate_polynomial",
        "(set-logic QF_NIA)\n(declare-fun x () Int)\n\
         (assert (= (+ (* x x) x (- 1)) 0))\n(check-sat)",
    ),
    // Fragments with long-standing separate evidence routes.
    (
        "qf_bv_unsat",
        "(set-logic QF_BV)\n(declare-fun a () (_ BitVec 4))\n(declare-fun b () (_ BitVec 4))\n\
         (assert (bvule a b))\n(assert (bvult b a))\n(check-sat)",
    ),
    (
        "qf_bv_sat",
        "(set-logic QF_BV)\n(declare-fun a () (_ BitVec 8))\n\
         (assert (bvult a #x05))\n(check-sat)",
    ),
    (
        "qf_lia_unsat",
        "(set-logic QF_LIA)\n(declare-fun x () Int)\n\
         (assert (> x 5))\n(assert (< x 3))\n(check-sat)",
    ),
    (
        "qf_lia_sat",
        "(set-logic QF_LIA)\n(declare-fun x () Int)\n(declare-fun y () Int)\n\
         (assert (> x 5))\n(assert (= y (+ x 1)))\n(check-sat)",
    ),
    (
        "qf_lra_unsat",
        "(set-logic QF_LRA)\n(declare-fun x () Real)\n\
         (assert (> x 1.0))\n(assert (< x 0.5))\n(check-sat)",
    ),
    (
        "qf_uf_unsat",
        "(set-logic QF_UF)\n(declare-fun p () Bool)\n\
         (assert p)\n(assert (not p))\n(check-sat)",
    ),
    (
        "qf_s_sat",
        "(set-logic QF_S)\n(declare-fun s () String)\n\
         (assert (= (str.len s) 3))\n(check-sat)",
    ),
];

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Verdict {
    Sat,
    Unsat,
    Unknown,
}

fn verdict_of_decision(result: &CheckResult) -> Verdict {
    match result {
        CheckResult::Sat(_) => Verdict::Sat,
        CheckResult::Unsat => Verdict::Unsat,
        CheckResult::Unknown(_) => Verdict::Unknown,
    }
}

fn verdict_of_evidence(evidence: &Evidence) -> Verdict {
    match evidence {
        Evidence::Sat(_) => Verdict::Sat,
        Evidence::Unknown(_) => Verdict::Unknown,
        // Every remaining variant is an `unsat` with some justification.
        _ => Verdict::Unsat,
    }
}

struct Row {
    name: &'static str,
    decision: Verdict,
    evidence: Verdict,
}

fn measure() -> Vec<Row> {
    let config = SolverConfig::default();
    QUERIES
        .iter()
        .map(|(name, text)| {
            // Independent parses: the two routes must agree about the QUERY, not
            // about one shared arena's state.
            let mut for_decision = parse_script(text).expect("query parses");
            let decision_assertions = for_decision.assertions.clone();
            let decided = solve(&mut for_decision.arena, &decision_assertions, &config)
                .expect("solve must not error");

            let mut for_evidence = parse_script(text).expect("query re-parses");
            let evidence_assertions = for_evidence.assertions.clone();
            let report = produce_evidence(&mut for_evidence.arena, &evidence_assertions, &config)
                .expect("evidence production must not error");

            Row {
                name,
                decision: verdict_of_decision(&decided),
                evidence: verdict_of_evidence(&report.evidence),
            }
        })
        .collect()
}

#[test]
fn a_decided_query_keeps_its_verdict_through_the_evidence_route() {
    let rows = measure();
    let mut violations = Vec::new();
    for row in &rows {
        println!(
            "  {:<34} decision={:<8?} evidence={:?}",
            row.name, row.decision, row.evidence
        );
        match (row.decision, row.evidence) {
            (Verdict::Unknown, _) => {}
            (d, e) if d == e => {}
            (d, Verdict::Unknown) => violations.push(format!(
                "{}: the decision route answered {d:?} and the evidence route gave up. \
                 A decided query whose artifact pipeline returns `unknown` is a capability \
                 lost between two implementations of the same question",
                row.name
            )),
            (d, e) => violations.push(format!(
                "{}: SOUNDNESS ALARM — decision route says {d:?}, evidence route says {e:?}",
                row.name
            )),
        }
    }
    assert!(violations.is_empty(), "{}", violations.join("\n"));
}

/// The invariant above is satisfiable by a corpus nothing decides, so this
/// requires the corpus to actually exercise both verdicts.
///
/// Without it, every query regressing to `unknown` on BOTH routes would leave
/// the agreement test green while the solver decided nothing at all.
#[test]
fn the_corpus_actually_decides_both_ways() {
    let rows = measure();
    let sat = rows.iter().filter(|r| r.decision == Verdict::Sat).count();
    let unsat = rows.iter().filter(|r| r.decision == Verdict::Unsat).count();
    assert!(
        sat >= 3,
        "only {sat} rows decided `sat`; the agreement check is then close to vacuous"
    );
    assert!(
        unsat >= 6,
        "only {unsat} rows decided `unsat`; the agreement check is then close to vacuous"
    );
}
