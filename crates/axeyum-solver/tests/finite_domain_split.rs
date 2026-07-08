//! Finite-domain disjunction case-split (`try_finite_domain_split`, an
//! `Unknown`-fallback in `check_auto`).
//!
//! A conjunction `D₁ ∧ … ∧ Dₘ ∧ rest`, where each `Dᵢ = (or (= v e₁) … (= v eₖ))`
//! is a disjunction of equalities, is satisfiable iff some choice of one equality
//! from each `Dᵢ` (plus `rest`) is — so all branches `unsat` ⇒ `unsat`, any branch
//! `sat` ⇒ `sat`. The route only fires on an otherwise-`Unknown` verdict, so these
//! rely on the disjunction+nonlinear shape defeating the primary routes.
//!
//! Soundness contract: never a wrong verdict. The SAT cases below pin the witness
//! exists (a genuinely satisfiable query must NOT be refuted), and the UNSAT cases
//! pin the refutation is real (a genuinely satisfiable query must NOT be called
//! `unsat`).

use std::time::Duration;

use axeyum_solver::{CheckResult, SolverConfig, solve_smtlib};

fn verdict(text: &str) -> CheckResult {
    let config = SolverConfig::default().with_timeout(Duration::from_secs(5));
    solve_smtlib(text, &config).expect("solve").result
}

/// The keystone `cli__regress1__nl__rewriting-sums` (`QF_NIA`, unsat): x∈{5,7,9},
/// y∈{x+1,x+2}, z∈{y+5,y+10} ⇒ z ≤ 21 ⇒ z² ≤ 441 < 10⁹, contradicting z² > 10⁹.
/// All 12 finite-domain branches propagate to a concrete z and refute the bound.
#[test]
fn rewriting_sums_is_unsat() {
    let text = r"
(set-logic QF_NIA)
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun z () Int)
(assert (or (= x 5) (= x 7) (= x 9)))
(assert (or (= y (+ x 1)) (= y (+ x 2))))
(assert (or (= z (+ y 5)) (= z (+ y 10))))
(assert (> (* z z) 1000000000))
(check-sat)
";
    assert_eq!(verdict(text), CheckResult::Unsat);
}

/// A finite-domain SAT: one branch (x=9) satisfies the nonlinear bound the
/// primary route stalls on. Must be decided `sat` (never falsely refuted).
#[test]
fn finite_domain_branch_sat() {
    let text = r"
(set-logic QF_NIA)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (or (= x 3) (= x 9)))
(assert (or (= y (* x x)) (= y (+ (* x x) 1))))
(assert (> y 50))
(check-sat)
";
    // x=9 ⇒ y ∈ {81,82} > 50 ⇒ sat. (x=3 ⇒ y ∈ {9,10}, not > 50.)
    assert!(matches!(verdict(text), CheckResult::Sat(_)));
}

/// A finite-domain UNSAT where NO branch works — every pinned value violates the
/// residual. Must be `unsat` (a real refutation).
#[test]
fn finite_domain_all_branches_unsat() {
    let text = r"
(set-logic QF_NIA)
(declare-fun x () Int)
(assert (or (= x 2) (= x 3) (= x 4)))
(assert (= (* x x) 1000))
(check-sat)
";
    // x∈{2,3,4} ⇒ x²∈{4,9,16}, never 1000 ⇒ unsat.
    assert_eq!(verdict(text), CheckResult::Unsat);
}

// ---------------------------------------------------------------------------
// Wrong-verdict-negatives: a genuinely SATISFIABLE finite-domain query must
// never be reported `Unsat`.
// ---------------------------------------------------------------------------

/// x∈{5,7,9}, and z² > 100 IS satisfiable (z from a large branch). Must not be
/// falsely refuted (the mirror of `rewriting_sums_is_unsat` with a reachable
/// bound).
#[test]
fn reachable_bound_not_refuted() {
    let text = r"
(set-logic QF_NIA)
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun z () Int)
(assert (or (= x 5) (= x 7) (= x 9)))
(assert (or (= y (+ x 1)) (= y (+ x 2))))
(assert (or (= z (+ y 5)) (= z (+ y 10))))
(assert (> (* z z) 100))
(check-sat)
";
    // z can be up to 21 ⇒ z² up to 441 > 100 ⇒ sat.
    assert_ne!(verdict(text), CheckResult::Unsat);
}
