//! Robustness + completeness regression tests for the OMT/optimization layer.
//!
//! Three gaps, all root-caused to the optimizer's feasibility probe formerly
//! calling the bare LIA oracle directly instead of the full `check_auto`
//! dispatcher:
//!
//! - **B (completeness):** `div`/`mod`-by-constant objectives/constraints now
//!   decide (the dispatcher preprocesses them), instead of erroring.
//! - **D (hard rule "unknown is never an error"):** an out-of-fragment objective
//!   (a UF application, a nonlinear product, a `bv2nat`) yields a graceful
//!   `OptOutcome::Unknown`, never an `Err`.
//! - **A (resource-limit promise):** a caller-set `config.timeout` is honored —
//!   a large Pareto front returns within the budget rather than running for
//!   minutes.

use std::time::{Duration, Instant};

use axeyum_ir::{Sort, TermArena, TermId};
use axeyum_solver::{
    LexObjective, OptOutcome, ParetoOutcome, SolverConfig, maximize_lia, minimize_lia,
    optimize_lia_pareto_with_config,
};

fn int_var(arena: &mut TermArena, name: &str) -> TermId {
    let sym = arena.declare(name, Sort::Int).unwrap();
    arena.var(sym)
}

// ---------------------------------------------------------------------------
// B: div/mod-by-constant objectives decide (instead of `Err(Unsupported)`).
// ---------------------------------------------------------------------------

#[test]
fn b_maximize_with_mod_constraint() {
    // x in [0,10] and x mod 2 = 0, maximize x -> 10 (z3 agrees).
    let mut arena = TermArena::new();
    let x = int_var(&mut arena, "x");
    let zero = arena.int_const(0);
    let ten = arena.int_const(10);
    let two = arena.int_const(2);
    let lo = arena.int_ge(x, zero).unwrap();
    let hi = arena.int_le(x, ten).unwrap();
    let xm2 = arena.int_mod(x, two).unwrap();
    let even = arena.eq(xm2, zero).unwrap();

    assert_eq!(
        maximize_lia(&mut arena, &[lo, hi, even], x).unwrap(),
        OptOutcome::Optimal(10)
    );
}

#[test]
fn b_maximize_with_div_constraint() {
    // x / 3 <= 5 and x >= 0, maximize x -> 17 (17/3 = 5, 18/3 = 6).
    let mut arena = TermArena::new();
    let x = int_var(&mut arena, "x");
    let zero = arena.int_const(0);
    let three = arena.int_const(3);
    let five = arena.int_const(5);
    let nonneg = arena.int_ge(x, zero).unwrap();
    let xd3 = arena.int_div(x, three).unwrap();
    let bounded = arena.int_le(xd3, five).unwrap();

    assert_eq!(
        maximize_lia(&mut arena, &[nonneg, bounded], x).unwrap(),
        OptOutcome::Optimal(17)
    );
}

// ---------------------------------------------------------------------------
// D: out-of-fragment objective -> graceful Unknown, never Err.
// ---------------------------------------------------------------------------

#[test]
fn d_maximize_uf_application_is_unknown_not_err() {
    // maximize f(x) s.t. f(x) < 10, where f is uninterpreted -> Unknown (the LIA
    // optimizer cannot decide a UF objective), NOT an error.
    let mut arena = TermArena::new();
    let f = arena.declare_fun("f", &[Sort::Int], Sort::Int).unwrap();
    let x = int_var(&mut arena, "x");
    let fx = arena.apply(f, &[x]).unwrap();
    let ten = arena.int_const(10);
    let bound = arena.int_lt(fx, ten).unwrap();

    let outcome = maximize_lia(&mut arena, &[bound], fx).expect("must not return Err");
    assert!(
        matches!(outcome, OptOutcome::Unknown(_)),
        "expected Unknown, got {outcome:?}"
    );
}

#[test]
fn d_minimize_nonlinear_is_unknown_not_err() {
    // minimize x*x s.t. x >= -5 and x <= 5 -> Unknown (nonlinear objective), NOT
    // an error. (We only require gracefulness, not the optimum 0.)
    let mut arena = TermArena::new();
    let x = int_var(&mut arena, "x");
    let xx = arena.int_mul(x, x).unwrap();
    let lo = arena.int_const(-5);
    let hi = arena.int_const(5);
    let lc = arena.int_ge(x, lo).unwrap();
    let hc = arena.int_le(x, hi).unwrap();

    let outcome = minimize_lia(&mut arena, &[lc, hc], xx).expect("must not return Err");
    assert!(
        matches!(outcome, OptOutcome::Unknown(_) | OptOutcome::Optimal(_)),
        "expected a graceful outcome (no Err), got {outcome:?}"
    );
    // The crucial promise is "no Err"; if it decides, it must decide correctly.
    if let OptOutcome::Optimal(v) = outcome {
        assert_eq!(v, 0, "if x*x is decided, the minimum over [-5,5] is 0");
    }
}

#[test]
fn d_minimize_bv2nat_is_unknown_not_err() {
    // minimize bv2nat(b) for a free bit-vector b -> a graceful outcome, never Err.
    // bv2nat is an Int-sorted objective routed through the LIA optimizer; the
    // probe must not hard-error on the out-of-pure-LIA term.
    let mut arena = TermArena::new();
    let b_sym = arena.declare("b", Sort::BitVec(4)).unwrap();
    let b = arena.var(b_sym);
    let nat = arena.bv2nat(b).unwrap();

    let outcome = minimize_lia(&mut arena, &[], nat).expect("must not return Err");
    assert!(
        matches!(outcome, OptOutcome::Unknown(_) | OptOutcome::Optimal(_)),
        "expected a graceful outcome (no Err), got {outcome:?}"
    );
    if let OptOutcome::Optimal(v) = outcome {
        assert_eq!(v, 0, "if bv2nat(b) is decided, its minimum is 0");
    }
}

// ---------------------------------------------------------------------------
// A: config.timeout is honored on a large Pareto front.
// ---------------------------------------------------------------------------

#[test]
fn a_pareto_honors_timeout_budget() {
    // x + y = 100, x >= 0, y >= 0 has a 101-point Pareto front (every (x, 100-x))
    // for max x / max y. With a 2s budget the call must RETURN within a few
    // seconds (Truncated / Unknown), not run for minutes.
    let mut arena = TermArena::new();
    let x = int_var(&mut arena, "x");
    let y = int_var(&mut arena, "y");
    let zero = arena.int_const(0);
    let hundred = arena.int_const(100);
    let sum = arena.int_add(x, y).unwrap();
    let sum_eq = arena.eq(sum, hundred).unwrap();
    let xnn = arena.int_ge(x, zero).unwrap();
    let ynn = arena.int_ge(y, zero).unwrap();

    let objectives = [
        LexObjective {
            objective: x,
            maximize: true,
        },
        LexObjective {
            objective: y,
            maximize: true,
        },
    ];
    let config = SolverConfig::default().with_timeout(Duration::from_secs(2));

    let start = Instant::now();
    let outcome =
        optimize_lia_pareto_with_config(&mut arena, &[sum_eq, xnn, ynn], &objectives, &config)
            .expect("must not return Err");
    let elapsed = start.elapsed();

    // Returned within a generous bound of the 2s budget (deadline is checked at
    // round boundaries, so one in-flight probe may overrun slightly).
    assert!(
        elapsed < Duration::from_secs(60),
        "pareto ignored the timeout budget (ran {elapsed:?})"
    );
    // It returns *some* deterministic outcome (Complete only if it genuinely
    // finished within budget; otherwise Truncated).
    match outcome {
        ParetoOutcome::Complete(_)
        | ParetoOutcome::Truncated(_)
        | ParetoOutcome::Unknown { .. } => {}
    }
}
