//! Interval bound-propagation refutation for `QF_NRA` (the `ones` class): a
//! polynomial atom whose interval — under the linear variable bounds — cannot
//! satisfy its own comparison is unsat. Sound (interval over-approximation),
//! incomplete. These lock the decided cases AND the soundness corners (a
//! satisfiable query must NEVER be wrongly refuted).
#![cfg(feature = "full")]
use std::time::Duration;

use axeyum_solver::{CheckResult, SolverConfig, solve_smtlib};

fn verdict(text: &str) -> CheckResult {
    solve_smtlib(
        text,
        &SolverConfig::new().with_timeout(Duration::from_secs(15)),
    )
    .expect("decides")
    .result
}
fn hdr(body: &str) -> String {
    format!(
        "(set-logic QF_NRA)(declare-fun a () Real)(declare-fun b () Real)(declare-fun c () Real)(declare-fun d () Real){body}(check-sat)"
    )
}

#[test]
fn ones_product_of_ge_one_is_unsat() {
    // a,b,c,d ≥ 1 ⊢ a·b·c·d ≥ 1, contradicting < 1 (cvc5 :status unsat).
    let t = hdr(
        "(assert (>= a 1))(assert (>= b 1))(assert (>= c 1))(assert (>= d 1))\
                 (assert (or (= a 1)(= b 1)(= c 1)(= d 1)))(assert (< (* a b c d) 1))",
    );
    assert_eq!(verdict(&t), CheckResult::Unsat);
}

#[test]
fn product_of_negatives_bound_is_unsat() {
    // a,b ∈ [−2,−1] ⇒ a·b ∈ [1,4]; a·b < 1 is infeasible.
    let t = hdr(
        "(assert (>= a (- 2)))(assert (<= a (- 1)))(assert (>= b (- 2)))(assert (<= b (- 1)))(assert (< (* a b) 1))",
    );
    assert_eq!(verdict(&t), CheckResult::Unsat);
}

#[test]
fn sign_crossing_product_lower_bound_is_unsat() {
    // a,b ∈ [−1,1] ⇒ a·b ∈ [−1,1]; a·b < −1 is infeasible.
    let t = hdr(
        "(assert (>= a (- 1)))(assert (<= a 1))(assert (>= b (- 1)))(assert (<= b 1))(assert (< (* a b) (- 1)))",
    );
    assert_eq!(verdict(&t), CheckResult::Unsat);
}

// --- SOUNDNESS: a satisfiable query must NOT be wrongly refuted --------------

#[test]
fn nonneg_product_below_one_is_not_unsat() {
    // a,b ≥ 0 ⇒ a·b ∈ [0,∞); a·b < 1 IS satisfiable (a=b=0). Must not refute.
    let t = hdr("(assert (>= a 0))(assert (>= b 0))(assert (< (* a b) 1))");
    assert_ne!(verdict(&t), CheckResult::Unsat);
}

#[test]
fn feasible_product_bound_is_not_unsat() {
    // a,b ≥ 1 ⇒ a·b ∈ [1,∞); a·b < 4 IS satisfiable (a=b=1). Must not refute.
    let t = hdr("(assert (>= a 1))(assert (>= b 1))(assert (< (* a b) 4))");
    assert_ne!(verdict(&t), CheckResult::Unsat);
}

#[test]
fn unbounded_variable_product_is_not_refuted() {
    // b has no bound ⇒ a·b interval is unbounded ⇒ no refutation (sat: a=1,b=0).
    let t = hdr("(assert (>= a 1))(assert (< (* a b) 1))");
    assert_ne!(verdict(&t), CheckResult::Unsat);
}
