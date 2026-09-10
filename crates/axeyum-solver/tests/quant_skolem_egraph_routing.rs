//! Capability pin: the Skolemized assertion set reaches the e-graph
//! instantiation loop even when trigger instantiation leaves no residual
//! quantifier.
//!
//! `prove_unsat_by_ematching` used to hand the Skolemized set to
//! [`qinst_egraph`]'s incremental loop only when `retried.residual_quantifier`
//! was true. That flag means "trigger instantiation did not consume every
//! quantifier in one pass" — a statement about the query's SHAPE, not about
//! whether the instances it produced suffice to refute. When they do not, the
//! loop built to select instances iteratively was never called at any budget.
//!
//! Measured 2026-09-10 on `bench-results/parity-losses-20260908/UF.txt` with
//! `AXEYUM_QPROBE=1` at a 24 s budget: of 62 entries into that function, 58
//! reported `residual=true` and took the existing branch, and 4 reported
//! `residual=false` and reached the decline having logged no
//! `skolemized-egraph` line at all. The file pinned here is one of the 4.
//!
//! **Why this test exists rather than a `corpus/regression/` entry.** That gate
//! is a soundness gate by construction — it *skips* `unknown`, so a regression
//! from `unsat` back to `unknown` would be counted as a coverage gap and the
//! suite would stay green. A capability needs an asserted verdict.
//!
//! **The guard is known to discriminate**, not assumed to: on the same binary
//! and the same 24 s budget this file returned `unknown` before the routing fix
//! and `unsat` after it. The refutation itself takes 96 ms of a 748 ms slice, so
//! this was never a budget question.
#![cfg(feature = "full")]

use std::thread;
use std::time::Duration;

use axeyum_solver::{CheckResult, SolverConfig, solve_smtlib};

/// SMT-LIB 2024 `UF/sledgehammer/Hoare/smtlib.1116374.smt2`, `:status unsat`.
/// z3 refutes it in 0.02 s with 2 quantifier instantiations.
const SLEDGEHAMMER_HOARE_1116374: &str = include_str!(
    "../../../corpus/public-curated/quantified/UF/smtlib-sledgehammer-clean/smtlib__UF__sledgehammer__Hoare__smtlib.1116374.smt2"
);

/// Generous relative to the measured 10.1 s front-door time, because this suite
/// shares a loaded box with other lanes. A regression returns `unknown`
/// promptly; it does not sit here burning the cap.
const BUDGET: Duration = Duration::from_secs(60);

/// The front door recurses over deeply nested `let`-bound UF terms, so it runs
/// on a worker with the same stack `corpus_regression` gives its solves.
const STACK: usize = 256 * 1024 * 1024;

#[test]
fn a_nested_negative_position_forall_is_refuted_through_the_front_door() {
    let outcome = thread::Builder::new()
        .stack_size(STACK)
        .spawn(|| {
            solve_smtlib(
                SLEDGEHAMMER_HOARE_1116374,
                &SolverConfig::default().with_timeout(BUDGET),
            )
        })
        .expect("spawn solver worker")
        .join()
        .expect("solver worker did not panic")
        .expect("front door runs");

    // Ground truth comes from the benchmark's own `:status`, read back through
    // the front door, not from a literal in this file -- so editing the vendored
    // benchmark cannot leave this assertion pinned to a status it no longer has.
    assert_eq!(
        outcome.expected_status.as_deref(),
        Some("unsat"),
        "the vendored benchmark lost the :status annotation this pin is anchored to"
    );

    let verdict = match &outcome.result {
        CheckResult::Unsat => "unsat",
        CheckResult::Sat(_) => "sat",
        CheckResult::Unknown(reason) => &reason.detail,
    };
    assert!(
        matches!(outcome.result, CheckResult::Unsat),
        "expected unsat, got `{verdict}`. The e-graph instantiation loop refutes \
         this in 96 ms once it is handed the Skolemized assertion set; `unknown` \
         means the routing regressed. See `skolemized_egraph_retry` in auto.rs and \
         re-measure with AXEYUM_QPROBE=1 -- a run that logs no `skolemized-egraph` \
         line never called the loop at all."
    );
}
