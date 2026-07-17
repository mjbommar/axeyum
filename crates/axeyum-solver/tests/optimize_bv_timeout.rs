//! "Never hang" regression tests for the bit-vector OMT layer.
//!
//! The BV optimizers formerly ran every inner feasibility probe with a hardcoded
//! `SolverConfig::default()` (timeout `None`), so a single hard BV probe could run
//! unboundedly regardless of the caller's `config.timeout`. The fix mirrors the
//! LIA/Real `*_with_config` deadline pattern for the bit-vector path.
//!
//! - **A (resource-limit promise):** a caller-set `config.timeout` is honored — a
//!   hard 64-bit Euclid-core query returns within the budget rather than spinning.
//! - The same query through the `Solver` façade with a configured timeout returns.
//! - A normal small BV optimize still returns the exact optimum (unchanged when no
//!   timeout fires).
#![cfg(feature = "full")]

use std::time::{Duration, Instant};

use axeyum_ir::{TermArena, TermId};
use axeyum_solver::{
    OptOutcome, SatBvBackend, Solver, SolverConfig, maximize_bv, maximize_bv_with_config,
    minimize_bv_with_config,
};

/// A 64-bit UNSAT "Euclid core": `q = x udiv d`, `r = x urem d`, `d != 0`, and
/// `¬(q·d + r = x)`. The reconstruction identity always holds, so the conjunction
/// is unsatisfiable — but it is a hard probe that runs unbounded without a deadline.
/// Returns `(assertions, x)` to optimize over.
fn euclid_core(arena: &mut TermArena) -> (Vec<TermId>, TermId) {
    let width = 64;
    let dividend = arena.bv_var("x", width).unwrap();
    let divisor = arena.bv_var("d", width).unwrap();
    let quotient = arena.bv_udiv(dividend, divisor).unwrap();
    let remainder = arena.bv_urem(dividend, divisor).unwrap();
    let zero = arena.bv_const(width, 0).unwrap();
    // d != 0
    let d_eq_0 = arena.eq(divisor, zero).unwrap();
    let d_ne_0 = arena.not(d_eq_0).unwrap();
    // ¬(q·d + r = x)
    let qd = arena.bv_mul(quotient, divisor).unwrap();
    let recon = arena.bv_add(qd, remainder).unwrap();
    let recon_eq_x = arena.eq(recon, dividend).unwrap();
    let not_recon = arena.not(recon_eq_x).unwrap();
    (vec![d_ne_0, not_recon], dividend)
}

#[test]
fn maximize_bv_with_config_honors_timeout() {
    // The hard UNSAT Euclid core, as `maximize_bv(x)`, must RETURN within a few
    // seconds under a 2s budget — not spin unbounded (the bug).
    let mut arena = TermArena::new();
    let (assertions, x) = euclid_core(&mut arena);
    let cfg = SolverConfig::default().with_timeout(Duration::from_secs(2));

    let start = Instant::now();
    let outcome = maximize_bv_with_config(&mut arena, &assertions, x, &cfg).unwrap();
    let elapsed = start.elapsed();

    // It returns (does not hang). Either an Unknown (resource limit / probe
    // undecided) or — if the probe happens to decide — a definite outcome; the
    // load-bearing property is that it returns promptly, well under the OS guard.
    assert!(
        elapsed < Duration::from_secs(20),
        "maximize_bv_with_config did not return promptly under a 2s budget ({elapsed:?})",
    );
    // The hard probe cannot certify an optimum under the budget, so the only sound
    // bounded results are Unknown or Infeasible — never a (wrong) finite optimum.
    assert!(
        matches!(outcome, OptOutcome::Unknown(_) | OptOutcome::Infeasible),
        "expected a graceful bounded result, got {outcome:?}",
    );
}

#[test]
fn facade_maximize_bv_honors_configured_timeout() {
    // The same hard query through the `Solver` façade with a configured timeout
    // must also return (the façade threads `self.config` into the optimizer).
    let mut arena = TermArena::new();
    let (assertions, x) = euclid_core(&mut arena);
    let mut solver = Solver::new(SatBvBackend::new());
    solver.set_config(SolverConfig::default().with_timeout(Duration::from_secs(2)));
    for a in assertions {
        solver.assert(a);
    }

    let start = Instant::now();
    let outcome = solver.maximize_bv(&mut arena, x).unwrap();
    let elapsed = start.elapsed();

    assert!(
        elapsed < Duration::from_secs(20),
        "façade maximize_bv did not return promptly under a 2s budget ({elapsed:?})",
    );
    assert!(
        matches!(outcome, OptOutcome::Unknown(_) | OptOutcome::Infeasible),
        "expected a graceful bounded result, got {outcome:?}",
    );
}

#[test]
fn small_bv_optimum_unchanged_with_and_without_timeout() {
    // A normal small BV optimize returns the exact optimum, and a generous timeout
    // does not change it (the `*_with_config` path is identical when no deadline
    // fires).
    let width = 8;
    let mut arena = TermArena::new();
    let x = arena.bv_var("x", width).unwrap();
    let bound = arena.bv_const(width, 10).unwrap();
    let le = arena.bv_uge(bound, x).unwrap(); // 10 >=u x, i.e. x <=u 10

    // No timeout: exact optimum 10.
    let no_cfg = maximize_bv(&mut arena, &[le], x).unwrap();
    assert_eq!(no_cfg, OptOutcome::Optimal(10));

    // Generous timeout (does not fire): same optimum.
    let cfg = SolverConfig::default().with_timeout(Duration::from_secs(60));
    let with_cfg = maximize_bv_with_config(&mut arena, &[le], x, &cfg).unwrap();
    assert_eq!(with_cfg, OptOutcome::Optimal(10));

    // Minimize is likewise unchanged: smallest unsigned x with x <=u 10 is 0.
    let min_cfg = minimize_bv_with_config(&mut arena, &[le], x, &cfg).unwrap();
    assert_eq!(min_cfg, OptOutcome::Optimal(0));
}
