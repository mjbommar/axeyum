//! When the preprocessed dispatch runs out of budget, the reduced solve's own
//! reason must survive the relabel.
//!
//! # The defect this gate exists for
//!
//! `dispatch_reduced` ends an out-of-budget reduced solve by replacing its
//! `UnknownReason` with the fixed sentence *"preprocessed dispatch timeout after
//! reduced solve"*. The reduced solve had already said **which route gave up and
//! on what bound**; the relabel dropped that and kept only the clock.
//!
//! That sentence is not a rare corner. It is the single largest named `Timeout`
//! detail on the parity board: 41 of 110 censused `QF_NIA` files
//! (`docs/research/03-measurements/qf-nia-is-not-a-width-problem-2026-09-12.md`),
//! 30 of the 260 `unknown`s across eleven divisions
//! (`docs/research/03-measurements/why-unknown-says-nothing-2026-09-11.md`), and
//! the leading class of this lane's `QF_NRA` census
//! (`bench-results/qf-nra-route-20260912/`). Every one of those rows had a
//! specific reason in hand and threw it away, so a census reading them could
//! only report "it ran out of time" for a third of a division.
//!
//! # Why this test cannot pass vacuously
//!
//! The property is an implication — *if* the detail is the preprocessed-timeout
//! relabel, *then* it carries the inner reason — and an implication whose
//! antecedent never fires is exactly the "checker that cannot fail" this
//! repository keeps re-learning about. So the test sweeps budgets, requires that
//! the relabel was reached **at least once**, and fails with an explicit
//! "fixture stopped covering the path" message if it was not.

#![cfg(feature = "full")]

use std::time::Duration;

use axeyum_solver::{CheckResult, SolverConfig, solve_smtlib};

/// A coupled three-variable nonlinear-real system in the MetiTarski/Horner
/// shape: bounded variables, nested products, no two-variable decomposition.
/// The exact deciders decline it and the linear-abstraction relaxation grinds,
/// so a small budget reliably expires inside the reduced dispatch.
const HARD_NRA: &str = r"
(set-logic QF_NRA)
(declare-fun a () Real)
(declare-fun b () Real)
(declare-fun c () Real)
(assert (> a 0))
(assert (< a 1))
(assert (> b 0))
(assert (< b 1))
(assert (> c 0))
(assert (< c 1))
(assert (> (* a (* a (* a (+ 1 (* b (* b (+ 2 (* c c)))))))) (+ 1 (* b (* c (* a b))))))
(assert (< (* a (+ 1 (* b (* c (+ 3 (* a (* b c))))))) (* c (* c (+ 1 (* a b))))))
(assert (= (+ (* a a) (+ (* b b) (* c c))) (/ 1 2)))
(check-sat)
";

/// The exact prefix `dispatch_reduced` relabels with. Kept byte-identical on
/// purpose so every existing consumer of this class still matches it.
const RELABEL_PREFIX: &str = "preprocessed dispatch timeout after reduced solve";

/// What the repair appends.
const CARRIER: &str = "the reduced solve's own reason was";

fn budgets() -> [u64; 7] {
    [10, 25, 50, 100, 200, 400, 800]
}

#[test]
fn the_preprocessed_timeout_relabel_carries_the_reduced_solves_own_reason() {
    let mut saw_relabel = 0usize;
    let mut details: Vec<String> = Vec::new();

    for ms in budgets() {
        let config = SolverConfig {
            timeout: Some(Duration::from_millis(ms)),
            ..SolverConfig::default()
        };
        let Ok(outcome) = solve_smtlib(HARD_NRA, &config) else {
            continue;
        };
        let CheckResult::Unknown(reason) = outcome.result else {
            continue;
        };
        details.push(format!("[{ms}ms] {}", reason.detail));
        if !reason.detail.starts_with(RELABEL_PREFIX) {
            continue;
        }
        saw_relabel += 1;
        assert!(
            reason.detail.contains(CARRIER),
            "the preprocessed-timeout relabel discarded the reduced solve's own \
             reason. At {ms}ms the detail was:\n  {}\nIt must keep the prefix AND \
             append what the reduced solve said.",
            reason.detail
        );
        // The carried half must be non-empty: appending the phrase and then an
        // empty string would satisfy the assertion above while carrying nothing.
        let carried = reason
            .detail
            .split(CARRIER)
            .nth(1)
            .unwrap_or("")
            .trim()
            .to_owned();
        assert!(
            carried.len() > 4,
            "the relabel names the carrier phrase but carries nothing after it: \
             {:?}",
            reason.detail
        );
    }

    assert!(
        saw_relabel > 0,
        "no budget in {:?}ms reached the preprocessed-timeout relabel at all, so \
         this gate measured NOTHING. The fixture has stopped covering the path \
         and must be replaced, not deleted. Details seen were:\n  {}",
        budgets(),
        details.join("\n  ")
    );
}

/// Control: with a generous budget this query does **not** produce the relabel,
/// so the assertion above is not satisfied by a detail the code emits
/// unconditionally.
#[test]
fn a_solve_that_does_not_run_out_of_budget_does_not_get_the_relabel() {
    let config = SolverConfig {
        timeout: Some(Duration::from_secs(30)),
        ..SolverConfig::default()
    };
    // Trivially decidable, and nothing to do with the clock.
    let outcome = solve_smtlib(
        r"
(set-logic QF_NRA)
(declare-fun x () Real)
(assert (> x 1))
(assert (< x 0))
(check-sat)
",
        &config,
    );
    match outcome.map(|o| o.result) {
        Ok(CheckResult::Unsat) => {}
        other => panic!("the control query must be decided `unsat`, got {other:?}"),
    }
}
