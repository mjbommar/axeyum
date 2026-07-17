//! Regression tests for the dedicated **UF × NRA** `check_auto` route: eager
//! Ackermann reduction of `Real → Real` uninterpreted applications feeding the NRA
//! decider (P1.6 slice). These pin the behavior the `qf_ufnra_differential_fuzz`
//! (z3-gated) proves sound in bulk: the `issue5836-2`-style congruence-forced
//! nonlinear contradiction decides `unsat`, a genuine model decides `sat` and is
//! replay-checked, the route is honored end-to-end under a deadline (past deadline →
//! `Unknown`, never a hang or a wrong verdict), and the linear `QF_UFLRA` path is not
//! hijacked.
#![cfg(feature = "full")]

use std::time::Duration;

use axeyum_ir::{Rational, Sort, TermArena, TermId, Value, eval};
use axeyum_solver::{CheckResult, RouteOutcome, SolverConfig, Verdict, check_auto_explained};

fn cfg() -> SolverConfig {
    SolverConfig::new().with_timeout(Duration::from_secs(10))
}
fn real(a: &mut TermArena, n: &str) -> TermId {
    let s = a.declare(n, Sort::Real).unwrap();
    a.var(s)
}
fn ri(a: &mut TermArena, n: i128) -> TermId {
    a.real_const(Rational::integer(n))
}

/// Whether the trace decided at the dedicated `uf-nra` route.
fn decided_via_uf_nra(trace: &axeyum_solver::RouteTrace, verdict: Verdict) -> bool {
    trace.attempts().iter().any(|a| {
        a.route == "uf-nra" && matches!(&a.outcome, RouteOutcome::Decided(v) if *v == verdict)
    })
}

/// The `issue5836-2` shape: congruence over a real UF forces a nonlinear
/// contradiction. `x = y ⇒ f(x) = f(y)`, but `f(x) = x·x` and `f(y) > y·y + 1`
/// with `x = y` gives `x·x = f(x) = f(y) > y·y + 1 = x·x + 1` — impossible.
#[test]
fn issue5836_2_congruence_forced_nonlinear_unsat() {
    let mut a = TermArena::new();
    let f = a.declare_fun("f", &[Sort::Real], Sort::Real).unwrap();
    let x = real(&mut a, "x");
    let y = real(&mut a, "y");
    let fx = a.apply(f, &[x]).unwrap();
    let fy = a.apply(f, &[y]).unwrap();
    let xx = a.real_mul(x, x).unwrap();
    let yy = a.real_mul(y, y).unwrap();
    let one = ri(&mut a, 1);
    let yy1 = a.real_add(yy, one).unwrap();
    let e1 = a.eq(x, y).unwrap();
    let e2 = a.eq(fx, xx).unwrap();
    let e3 = a.real_gt(fy, yy1).unwrap();

    let (result, trace) = check_auto_explained(&mut a, &[e1, e2, e3], &cfg()).unwrap();
    assert!(
        matches!(result, CheckResult::Unsat),
        "congruence-forced nonlinear contradiction must be unsat, got {result:?}"
    );
    assert!(
        decided_via_uf_nra(&trace, Verdict::Unsat),
        "must decide at the dedicated uf-nra route, trace: {trace}"
    );
}

/// A satisfiable UF × NRA query: `f(x)·f(x) = 2` (take `f(x) = √2`). The returned
/// `sat` model must carry a real-UF interpretation and replay against the original.
#[test]
fn uf_result_squared_is_sat_and_replays() {
    let mut a = TermArena::new();
    let f = a.declare_fun("f", &[Sort::Real], Sort::Real).unwrap();
    let x = real(&mut a, "x");
    let fx = a.apply(f, &[x]).unwrap();
    let sq = a.real_mul(fx, fx).unwrap();
    let two = ri(&mut a, 2);
    let e = a.eq(sq, two).unwrap();

    let (result, trace) = check_auto_explained(&mut a, &[e], &cfg()).unwrap();
    let CheckResult::Sat(model) = result else {
        panic!("f(x)*f(x) = 2 must be sat, got {result:?}");
    };
    assert!(
        decided_via_uf_nra(&trace, Verdict::Sat),
        "must decide at the dedicated uf-nra route, trace: {trace}"
    );
    // The soundness anchor: the model replays against the ORIGINAL assertion.
    let assignment = model.to_assignment();
    assert!(
        matches!(eval(&a, e, &assignment), Ok(Value::Bool(true))),
        "returned sat model must satisfy the original f(x)*f(x) = 2"
    );
}

/// A pure-sign nonlinear contradiction guarded by a UF atom:
/// `f(x) > 0 ∧ x·x < 0` — unsat because `x·x < 0` is unsatisfiable over the reals,
/// independent of `f`. Exercises the route on a UF application appearing only
/// linearly beside a nonlinear atom.
#[test]
fn uf_atom_beside_negative_square_is_unsat() {
    let mut a = TermArena::new();
    let f = a.declare_fun("f", &[Sort::Real], Sort::Real).unwrap();
    let x = real(&mut a, "x");
    let fx = a.apply(f, &[x]).unwrap();
    let xx = a.real_mul(x, x).unwrap();
    let zero = ri(&mut a, 0);
    let e1 = a.real_gt(fx, zero).unwrap();
    let e2 = a.real_lt(xx, zero).unwrap();

    let (result, _trace) = check_auto_explained(&mut a, &[e1, e2], &cfg()).unwrap();
    assert!(
        matches!(result, CheckResult::Unsat),
        "f(x) > 0 ∧ x*x < 0 must be unsat, got {result:?}"
    );
}

/// Deadline regression: with an already-exhausted budget the route must return
/// `Unknown` immediately — never a hang, never a wrong verdict. A `Duration::ZERO`
/// timeout makes every deadline check fire on entry.
#[test]
fn past_deadline_is_immediate_unknown() {
    let mut a = TermArena::new();
    let f = a.declare_fun("f", &[Sort::Real], Sort::Real).unwrap();
    let x = real(&mut a, "x");
    let fx = a.apply(f, &[x]).unwrap();
    let sq = a.real_mul(fx, fx).unwrap();
    let two = ri(&mut a, 2);
    let e = a.eq(sq, two).unwrap();

    let zero_budget = SolverConfig::new().with_timeout(Duration::ZERO);
    let start = std::time::Instant::now();
    let (result, _trace) = check_auto_explained(&mut a, &[e], &zero_budget).unwrap();
    assert!(
        matches!(result, CheckResult::Unknown(_)),
        "an exhausted budget must yield Unknown, got {result:?}"
    );
    assert!(
        start.elapsed() < Duration::from_secs(1),
        "past-deadline dispatch must return promptly, took {:?}",
        start.elapsed()
    );
}

/// The linear `QF_UFLRA` path must NOT be hijacked by the nonlinear route: a purely
/// linear UF+real query (`f(x) = 1 ∧ f(y) = 2 ∧ x = y`, congruence-unsat) is left
/// to the existing UF+LRA combination — `uf-nra` never appears in its trace.
#[test]
fn linear_uflra_is_not_routed_through_uf_nra() {
    let mut a = TermArena::new();
    let f = a.declare_fun("f", &[Sort::Real], Sort::Real).unwrap();
    let x = real(&mut a, "x");
    let y = real(&mut a, "y");
    let fx = a.apply(f, &[x]).unwrap();
    let fy = a.apply(f, &[y]).unwrap();
    let one = ri(&mut a, 1);
    let two = ri(&mut a, 2);
    let e1 = a.eq(fx, one).unwrap();
    let e2 = a.eq(fy, two).unwrap();
    let e3 = a.eq(x, y).unwrap();

    let (result, trace) = check_auto_explained(&mut a, &[e1, e2, e3], &cfg()).unwrap();
    assert!(
        matches!(result, CheckResult::Unsat),
        "linear UF congruence conflict must be unsat, got {result:?}"
    );
    assert!(
        !trace.attempts().iter().any(|att| att.route == "uf-nra"),
        "linear QF_UFLRA must not be routed through uf-nra, trace: {trace}"
    );
}
