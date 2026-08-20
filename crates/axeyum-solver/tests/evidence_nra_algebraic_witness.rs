//! Route agreement on an NRA `sat` with a real-**algebraic** witness.
//!
//! The DECISION route (`check_auto_explained`) and the EVIDENCE route
//! (`produce_evidence`) run the same exact real-root decider, but only the
//! evidence route replays its candidate model through the ground evaluator
//! (`nra::check_with_nra`'s final soundness guard). When the witness is a
//! `Value::RealAlgebraic`, that replay needs *algebraic field arithmetic* — and a
//! rational operand used to defeat it, so the guard downgraded a genuinely
//! satisfiable query to `unknown` while the decision route reported `sat`.
//!
//! `cli__regress0__nl__issue3003.smt2` (cvc5 regress, declared `:status sat`) is
//! the instance: `x ≥ 0 ∧ x² = 1 + y·(y·(−1))`. The witness `x = 1/2`,
//! `y = −√3/2` makes the right-hand side `1 + (−3/4)` — a rational **added to** an
//! algebraic, which is exactly the shape that declined.
//!
//! The assertion here is not "the evidence route returns `sat`" but the repo Hard
//! Rule: a `sat` is only worth anything if the lifted model **replays against the
//! original term**. So the test demands `EvidenceCheck::Verified`, which
//! re-evaluates the assertions; a producer that started claiming `sat` without a
//! replayable model would fail it rather than pass it.
#![cfg(feature = "full")]

use axeyum_solver::{
    CheckResult, Evidence, EvidenceCheck, SolverConfig, check_auto_explained,
    produce_evidence_smtlib_with_script,
};

/// The cvc5 regress instance, verbatim in the parts that matter.
const ISSUE3003: &str = "\
(set-logic QF_NRA)
(set-info :status sat)
(declare-fun x () Real)
(declare-fun y () Real)
(assert (let ((?v_1 (<= 0.0 x)))
  (and ?v_1 (and ?v_1 (and ?v_1 (= (* x x) (+ 1 (* y (* y (- 1))))))))))
(check-sat)
";

#[test]
fn issue3003_decision_and_evidence_routes_agree_on_sat() {
    let config = SolverConfig::new();

    let mut script = axeyum_smtlib::parse_script(ISSUE3003).expect("parse");
    let assertions = script.assertions.clone();
    let (decision, _trace) =
        check_auto_explained(&mut script.arena, &assertions, &config).expect("decide");
    assert!(
        matches!(decision, CheckResult::Sat(_)),
        "declared `:status sat`; decision route said {decision:?}"
    );

    let produced = produce_evidence_smtlib_with_script(ISSUE3003, &config).expect("evidence");
    assert!(
        matches!(produced.report.evidence, Evidence::Sat(_)),
        "evidence route must agree with the decision route, got {:?}",
        produced.report.evidence
    );
    assert_eq!(
        produced.check_outcome().expect("re-check"),
        EvidenceCheck::Verified,
        "the `sat` model must replay against the original term"
    );
}
