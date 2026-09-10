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

/// The SOUND-1 query: `(= y 0) ∧ (= x 5) ∧ (= (/ x y) 100) ∧ (= (f x) 7)`.
///
/// Satisfiable, and only through a chosen interpretation of the SMT-LIB
/// unspecified `(/ 5 0)` — the total evaluator convention is `x/0 = 0`, so a
/// model that does not carry the witness `5/0 → 100` cannot satisfy conjunct 2.
/// The `(= (f x) 7)` conjunct is what pulls the query onto the UF × NRA routes.
fn div_at_zero_query(a: &mut TermArena) -> [TermId; 4] {
    let f = a.declare_fun("f", &[Sort::Real], Sort::Real).unwrap();
    let x = real(a, "wx");
    let y = real(a, "wy");
    let zero = ri(a, 0);
    let five = ri(a, 5);
    let seven = ri(a, 7);
    let hundred = ri(a, 100);
    let quotient = a.real_div(x, y).unwrap();
    let fx = a.apply(f, &[x]).unwrap();
    [
        a.eq(y, zero).unwrap(),
        a.eq(x, five).unwrap(),
        a.eq(quotient, hundred).unwrap(),
        a.eq(fx, seven).unwrap(),
    ]
}

/// The two configurations this query is checked under, because **they take
/// different routes** and only one of them reproduced the defect.
///
/// Measured on the fix commit: under `SolverConfig::default()` (no timeout) the
/// preprocessed path errors, the trace records
/// `preprocess: declined (incomplete: preprocessed path errored; degraded to the
/// original query)`, and `uf-nra` decides — that is the arm SOUND-1 shipped on.
/// Under a 10 s budget the preprocessed path succeeds instead and `uf-arithmetic`
/// decides. A test pinned to one config would have been green on the other while
/// the defect stood, so both are checked and neither is pinned to a route name.
fn div_at_zero_configs() -> [(&'static str, SolverConfig); 2] {
    [
        (
            "default (no timeout) — the arm SOUND-1 shipped on",
            SolverConfig::default(),
        ),
        ("10s budget", cfg()),
    ]
}

/// **SOUND-1 regression.** `check_auto` returned `Sat` on the query above with a
/// model that did NOT replay — the third conjunct evaluated `Bool(false)` against
/// `model.to_assignment()`, violating the repository's hard rule that every `sat`
/// must be checkable by evaluating the original term against the lifted model.
///
/// The defect was **not** a missing replay. `dispatch_uf_nra` replays, and its
/// replay passed: it ran against `projected`, an `Assignment` that carried the
/// chosen division-at-zero witness `5/0 → 100`. `euf::project_replay_build` then
/// built the emitted `Model` from that assignment copying only symbol values and
/// function interpretations, dropping `real_div_zero`. The caller's `(/ 5 0)`
/// therefore fell back to the total `x/0 = 0` convention and the conjunct was
/// false. The certificate did not carry a distinction its producer made.
///
/// This test replays through `model.to_assignment()` — the artifact a CALLER
/// receives — deliberately, not through any internal state.
///
/// **What each revert does**, measured, because "it fails if you revert the fix"
/// is not one statement when the fix has two halves:
///
/// - revert BOTH halves of the `project_replay_build` fix → wrong `Sat`, and THIS
///   test fails on the default config (`assertion #2` is `Bool(false)`);
/// - revert only the `real_div_zeros` carry → the second replay catches it and the
///   verdict degrades to a sound `Unknown`, which this test deliberately
///   tolerates. [`div_at_zero_query_is_still_decided_sat`] is the test that dies
///   on that revert;
/// - revert only the second replay → nothing observable changes today. That guard
///   is reachable only through a component the model build forgets, and after the
///   carry there is none: `Assignment` holds exactly bindings, functions and
///   `real_div_zero`, all three of which `Model` carries. It is a forward guard
///   against the next such component, not a live check, and this comment says so
///   rather than letting a green suite imply otherwise.
///
/// `unknown` is a sound outcome here and the assertion admits it; what it forbids
/// is a `Sat` that does not replay.
#[test]
fn div_at_zero_witness_survives_into_the_emitted_model() {
    for (label, config) in div_at_zero_configs() {
        let mut a = TermArena::new();
        let asserts = div_at_zero_query(&mut a);
        let (result, trace) = check_auto_explained(&mut a, &asserts, &config).unwrap();
        match &result {
            CheckResult::Sat(model) => {
                let assignment = model.to_assignment();
                for (index, &assertion) in asserts.iter().enumerate() {
                    assert_eq!(
                        eval(&a, assertion, &assignment),
                        Ok(Value::Bool(true)),
                        "[{label}] sat model must replay original assertion #{index} \
                         (SOUND-1: it evaluated false because the emitted model \
                         dropped the division-at-zero witness); trace: {trace}"
                    );
                }
                // The witness must be PRESENT, not merely consistent by luck:
                // `(/ 5 0) = 100` is only representable through `real_div_zero`.
                assert_eq!(
                    model.real_div_zero(Rational::integer(5)),
                    Some(Rational::integer(100)),
                    "[{label}] the emitted model must carry the chosen (/ 5 0) \
                     interpretation; trace: {trace}"
                );
            }
            CheckResult::Unsat => {
                panic!("[{label}] the query is satisfiable, got unsat; trace: {trace}")
            }
            // A sound decline is acceptable; a non-replaying `sat` is not.
            CheckResult::Unknown(_) => {}
        }
    }
}

/// Companion to [`div_at_zero_witness_survives_into_the_emitted_model`]: the
/// solver must still DECIDE this query, not retreat to `Unknown`.
///
/// The two are deliberately separate. The soundness test tolerates `Unknown`,
/// because a sound decline beats a wrong `sat` — but that tolerance is exactly
/// what makes it survive a revert of the `real_div_zeros` carry alone (the second
/// replay then turns the incomplete model into an `Unknown`). This test is the one
/// that dies on that revert, so the pair distinguishes "we stopped emitting a
/// wrong answer" from "we stopped emitting an answer".
///
/// It asserts the VERDICT, not the route: which route decides depends on the
/// budget (see [`div_at_zero_configs`]), and pinning a route name here would make
/// this a routing test rather than a capability one.
#[test]
fn div_at_zero_query_is_still_decided_sat() {
    for (label, config) in div_at_zero_configs() {
        let mut a = TermArena::new();
        let asserts = div_at_zero_query(&mut a);
        let (result, trace) = check_auto_explained(&mut a, &asserts, &config).unwrap();
        assert!(
            matches!(result, CheckResult::Sat(_)),
            "[{label}] the div-at-zero query is satisfiable and the routes can build \
             the witness; an Unknown here means the emitted model lost a component \
             the producer chose and a replay declined. Got {result:?}; trace: {trace}"
        );
    }
}
