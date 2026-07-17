//! Deadline-honored regression for the bounded ADR-0029 string route on a
//! `str.replace` mixed with a `str.in_re` membership.
//!
//! Found by the Phase D fuzz (commit d124f427, finding #1): a `str.replace` over
//! strings combined with a regex membership drives the bounded pre-check encoder's
//! downstream LIA path into a **deadline-blind hang**. The hang was NOT in the
//! bit-blast/SAT solve (a tiny ~3k-clause CNF that solves in milliseconds) but in
//! the online DPLL(T) LIA atom collector (`collect_lia_atoms`), which walked the
//! heavily-shared assertion DAG (the `str.replace` result feeds many `str.in_re`
//! NFA positions) **without interior-node memoization** — exponential re-descent
//! that ran for ~6 s under a 200 ms budget (a ~30x overrun) before any timeout
//! check fired. Memoizing every visited node makes the walk linear and restores
//! deadline honoring. Never a wrong verdict — deadline expiry is `Unknown`.
//!
//! Each case runs on a worker thread under a generous-but-finite wall cap so a
//! regression cannot hang CI: it fails loudly instead.
#![cfg(feature = "full")]

use std::sync::mpsc;
use std::thread;
use std::time::{Duration, Instant};

use axeyum_solver::{CheckResult, SolverConfig, solve_smtlib};

/// Solves `script` under `timeout` on a worker thread, failing if it does not
/// return within `wall_cap` (so a re-introduced hang fails instead of blocking CI).
/// Returns the elapsed wall time and the verdict.
fn solve_capped(
    script: &'static str,
    timeout: Duration,
    wall_cap: Duration,
) -> (Duration, CheckResult) {
    let (tx, rx) = mpsc::channel();
    let cfg = SolverConfig::new().with_timeout(timeout);
    let start = Instant::now();
    thread::spawn(move || {
        let verdict = solve_smtlib(script, &cfg).map(|o| o.result);
        let _ = tx.send((start.elapsed(), verdict));
    });
    let Ok((elapsed, verdict)) = rx.recv_timeout(wall_cap) else {
        panic!(
            "DEADLINE HOLE REGRESSED: the str.replace×membership shape did not return \
             within the {wall_cap:?} wall cap under a {timeout:?} timeout (the collector \
             re-descended the shared DAG exponentially again)"
        );
    };
    match verdict {
        Ok(result) => (elapsed, result),
        Err(error) => panic!("solve_smtlib errored: {error:?}"),
    }
}

/// The minimal hanging shape: a `str.replace` over a symbolic string feeding a
/// regex membership, plus a length constraint (so `str.len` lowers to the LIA path
/// whose atom collector held the deadline-blind exponential walk).
const SCRIPT: &str = r#"(set-logic QF_S)
(declare-const x String)
(assert (str.in_re (str.replace x "a" "bb") (re.* (re.range "a" "z"))))
(assert (= (str.len x) 6))
(check-sat)"#;

#[test]
fn replace_membership_honors_a_tight_deadline() {
    // A 200 ms budget must yield a fast, sound verdict — not a ~6 s grind. Before
    // the fix this returned `Unknown(Timeout)` only after ~6.2 s; assert it now
    // returns well under 3 s (a comfortable ceiling above the fixed ~0.3 s while
    // still far below the old hang).
    let (elapsed, result) =
        solve_capped(SCRIPT, Duration::from_millis(200), Duration::from_secs(30));
    assert!(
        elapsed < Duration::from_secs(3),
        "expected a deadline-honored return well under 3s, took {elapsed:?}"
    );
    // Either a sound definite verdict or a first-class Unknown is acceptable under a
    // tight budget — never a wrong verdict, never a hang.
    assert!(
        matches!(
            result,
            CheckResult::Sat(_) | CheckResult::Unsat | CheckResult::Unknown(_)
        ),
        "unexpected result shape: {result:?}"
    );
}

#[test]
fn replace_membership_decides_under_a_generous_deadline() {
    // With budget to spare the shape is now *decided* quickly (the linear collector
    // no longer burns the budget), not merely declined — a capability win. The
    // shape is satisfiable (a length-6 string over 'a'..'z').
    let (elapsed, result) = solve_capped(SCRIPT, Duration::from_secs(20), Duration::from_secs(30));
    assert!(
        elapsed < Duration::from_secs(5),
        "expected a quick decision, took {elapsed:?}"
    );
    assert!(
        matches!(result, CheckResult::Sat(_)),
        "expected Sat for the length-6 membership shape, got {result:?}"
    );
}
