//! Robustness + completeness regression tests for the OMT/optimization layer.
//!
//! Three gaps, all root-caused to the optimizer's feasibility probe formerly
//! calling the bare LIA oracle directly instead of the full `check_auto`
//! dispatcher:
//!
//! - **B (completeness):** `div`/`mod`-by-constant objectives/constraints now
//!   decide (the dispatcher preprocesses them), instead of erroring.
//! - **D (hard rule "unknown is never an error"):** an out-of-fragment objective
//!   (a nonlinear product, a `bv2nat`) yields a graceful `OptOutcome::Unknown`,
//!   never an `Err`. (An arith-sorted UF-application objective is now decidable
//!   via the replay-checked combined path, so it may instead return a correct
//!   `Optimal` — still graceful, never `Err`.)
//! - **A (resource-limit promise):** a caller-set `config.timeout` is honored —
//!   a large Pareto front returns within the budget rather than running for
//!   minutes.
#![cfg(feature = "full")]

use std::time::{Duration, Instant};

use axeyum_ir::{Sort, TermArena, TermId};
use axeyum_solver::{
    BvLexObjective, LexObjective, OptOutcome, ParetoOutcome, SolverConfig, UnknownKind,
    maximize_lia, maximize_lia_with_config, minimize_lia, optimize_bv_pareto,
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
fn d_maximize_uf_application_is_graceful_never_err() {
    // maximize f(x) s.t. f(x) < 10, where f is uninterpreted. The arith-sorted UF
    // sat-model projection is now replay-checked through the combined path, so the
    // optimizer can decide this objective: the integer supremum of f(x) subject to
    // f(x) < 10 is 9 (f uninterpreted, so f(x) may take any integer below 10). The
    // hard-rule guarantee stands — it is graceful (never `Err`); previously it
    // declined to `Unknown`, now it decides `Optimal(9)`. Either is acceptable as
    // long as the result is never `Err` and any optimum is correct.
    let mut arena = TermArena::new();
    let f = arena.declare_fun("f", &[Sort::Int], Sort::Int).unwrap();
    let x = int_var(&mut arena, "x");
    let fx = arena.apply(f, &[x]).unwrap();
    let ten = arena.int_const(10);
    let bound = arena.int_lt(fx, ten).unwrap();

    let outcome = maximize_lia(&mut arena, &[bound], fx).expect("must not return Err");
    assert!(
        matches!(outcome, OptOutcome::Unknown(_) | OptOutcome::Optimal(9)),
        "expected a graceful Unknown or the correct Optimal(9), got {outcome:?}"
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

#[test]
fn d_bv_pareto_non_bv_objective_is_unknown_not_err() {
    // A caller bug or frontend mismatch can pass an Int term through the BV
    // Pareto API. This should be a graceful Unknown, matching LIA Pareto's
    // out-of-fragment behavior, not a hard solver error.
    let mut arena = TermArena::new();
    let x = int_var(&mut arena, "not_bv_obj");
    let zero = arena.int_const(0);
    let pin = arena.eq(x, zero).unwrap();
    let objectives = [BvLexObjective {
        objective: x,
        signed: false,
        maximize: true,
    }];

    let outcome = optimize_bv_pareto(&mut arena, &[pin], &objectives).expect("must not return Err");
    assert!(
        matches!(outcome, ParetoOutcome::Unknown { .. }),
        "expected a graceful Unknown for a non-BV Pareto objective, got {outcome:?}"
    );
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

// CON-5: an unbounded verdict needs a preserving direction, not a search cap.
#[test]
fn improving_ray_preserves_coupled_equalities() {
    let mut arena = TermArena::new();
    let x = int_var(&mut arena, "ray_x");
    let y = int_var(&mut arena, "ray_y");
    let zero = arena.int_const(0);
    let two = arena.int_const(2);
    let twice_x = arena.int_mul(two, x).unwrap();
    let coupling = arena.eq(y, twice_x).unwrap();
    let nonnegative = arena.int_ge(x, zero).unwrap();
    assert_eq!(
        maximize_lia(&mut arena, &[coupling, nonnegative], y).unwrap(),
        OptOutcome::Unbounded
    );
}

#[test]
fn ray_cannot_ignore_a_coupled_upper_bound() {
    let mut arena = TermArena::new();
    let x = int_var(&mut arena, "bounded_ray_x");
    let y = int_var(&mut arena, "bounded_ray_y");
    let zero = arena.int_const(0);
    let ten = arena.int_const(10);
    let coupling = arena.eq(y, x).unwrap();
    let upper = arena.int_le(y, ten).unwrap();
    let lower = arena.int_ge(x, zero).unwrap();
    assert_eq!(
        maximize_lia(&mut arena, &[coupling, upper, lower], x).unwrap(),
        OptOutcome::Optimal(10)
    );
}

#[test]
fn ray_preserves_strict_and_negated_inequalities() {
    let mut arena = TermArena::new();
    let x = int_var(&mut arena, "strict_ray_x");
    let ten = arena.int_const(10);
    let le = arena.int_le(x, ten).unwrap();
    let gt = arena.not(le).unwrap();
    assert_eq!(
        maximize_lia(&mut arena, &[gt], x).unwrap(),
        OptOutcome::Unbounded
    );
    let lt = arena.int_lt(x, ten).unwrap();
    let zero = arena.int_const(0);
    let lower = arena.int_ge(x, zero).unwrap();
    assert_eq!(
        maximize_lia(&mut arena, &[lt, lower], x).unwrap(),
        OptOutcome::Optimal(9)
    );
}

#[test]
fn representational_ceiling_is_not_an_unboundedness_witness() {
    let mut arena = TermArena::new();
    let x = int_var(&mut arena, "ceiling_x");
    let ceiling = arena.int_const(i128::MAX);
    let pin = arena.eq(x, ceiling).unwrap();
    let config = SolverConfig::default().with_timeout(Duration::from_secs(2));
    let outcome = maximize_lia_with_config(&mut arena, &[pin], x, &config).unwrap();
    assert!(
        matches!(
            outcome,
            OptOutcome::Unknown(_) | OptOutcome::Optimal(i128::MAX)
        ),
        "a fixed finite objective cannot be unbounded: {outcome:?}"
    );
}

#[test]
fn nonlinear_bounded_domain_cannot_be_homogenized_as_a_linear_ray() {
    let mut arena = TermArena::new();
    let x = int_var(&mut arena, "nonlinear_ray_x");
    let square = arena.int_mul(x, x).unwrap();
    let hundred = arena.int_const(100);
    let zero = arena.int_const(0);
    let upper = arena.int_le(square, hundred).unwrap();
    let lower = arena.int_ge(x, zero).unwrap();
    let config = SolverConfig::default().with_timeout(Duration::from_millis(200));
    let outcome = maximize_lia_with_config(&mut arena, &[upper, lower], x, &config).unwrap();
    assert!(
        matches!(outcome, OptOutcome::Unknown(_) | OptOutcome::Optimal(10)),
        "{outcome:?}"
    );
}

#[test]
fn integer_optimization_zero_budget_never_starts_a_probe() {
    let mut arena = TermArena::new();
    let x = int_var(&mut arena, "expired_x");
    let config = SolverConfig::default().with_timeout(Duration::ZERO);
    let outcome = maximize_lia_with_config(&mut arena, &[], x, &config).unwrap();
    assert!(
        matches!(outcome, OptOutcome::Unknown(ref reason) if reason.kind == UnknownKind::ResourceLimit)
    );
}

#[test]
fn ray_negative_coefficient_preserves_the_actual_upper_bound() {
    let mut arena = TermArena::new();
    let x = int_var(&mut arena, "negative_coefficient_ray_x");
    let minus_one = arena.int_const(-1);
    let minus_ten = arena.int_const(-10);
    let zero = arena.int_const(0);
    let negative_x = arena.int_mul(minus_one, x).unwrap();
    let upper = arena.int_ge(negative_x, minus_ten).unwrap();
    let lower = arena.int_ge(x, zero).unwrap();
    assert_eq!(
        maximize_lia(&mut arena, &[upper, lower], x).unwrap(),
        OptOutcome::Optimal(10)
    );
}

#[test]
fn affine_optimization_matches_an_independent_finite_population() {
    // Exhaustive witnesses supply the expected answer without sharing the ray
    // or bound-search code. Explicit seed and small exact integer domain.
    let mut seed = 0x2300_2026_1010_u64;
    let mut coefficient = || {
        seed = seed.wrapping_mul(6_364_136_223_846_793_005).wrapping_add(1);
        i128::from((seed >> 32) as u32 % 7) - 3
    };
    for case in 0..128 {
        let constraint_x = coefficient();
        let constraint_y = coefficient();
        let cap = coefficient();
        let objective_x = coefficient();
        let objective_y = coefficient();
        let offset = coefficient();
        let expected = (-4_i128..=4)
            .flat_map(|x| (-4_i128..=4).map(move |y| (x, y)))
            .filter(|&(x, y)| constraint_x * x + constraint_y * y <= cap)
            .map(|(x, y)| objective_x * x + objective_y * y + offset)
            .max();
        let mut arena = TermArena::new();
        let x = int_var(&mut arena, "finite_x");
        let y = int_var(&mut arena, "finite_y");
        let lower = arena.int_const(-4);
        let upper = arena.int_const(4);
        let mut assertions = vec![
            arena.int_ge(x, lower).unwrap(),
            arena.int_le(x, upper).unwrap(),
            arena.int_ge(y, lower).unwrap(),
            arena.int_le(y, upper).unwrap(),
        ];
        let ac = arena.int_const(constraint_x);
        let bc = arena.int_const(constraint_y);
        let ax = arena.int_mul(ac, x).unwrap();
        let by = arena.int_mul(bc, y).unwrap();
        let lhs = arena.int_add(ax, by).unwrap();
        let cap_term = arena.int_const(cap);
        assertions.push(arena.int_le(lhs, cap_term).unwrap());
        let cc = arena.int_const(objective_x);
        let dc = arena.int_const(objective_y);
        let cx = arena.int_mul(cc, x).unwrap();
        let dy = arena.int_mul(dc, y).unwrap();
        let sum = arena.int_add(cx, dy).unwrap();
        let offset_term = arena.int_const(offset);
        let objective = arena.int_add(sum, offset_term).unwrap();
        let outcome = maximize_lia(&mut arena, &assertions, objective).unwrap();
        assert_eq!(
            outcome,
            expected.map_or(OptOutcome::Infeasible, OptOutcome::Optimal),
            "finite case {case}: constraint {constraint_x}x + {constraint_y}y <= {cap}, objective {objective_x}x + {objective_y}y + {offset}"
        );
    }
}

#[test]
fn exhausted_budget_stops_every_single_bv_optimizer() {
    use axeyum_solver::{
        maximize_bv_signed_with_config, maximize_bv_with_config, minimize_bv_signed_with_config,
        minimize_bv_with_config,
    };
    let mut arena = TermArena::new();
    let symbol = arena.declare("budget_bv", Sort::BitVec(8)).unwrap();
    let objective = arena.var(symbol);
    let config = SolverConfig {
        timeout: Some(Duration::ZERO),
        ..SolverConfig::default()
    };
    for optimize in [
        maximize_bv_with_config,
        minimize_bv_with_config,
        maximize_bv_signed_with_config,
        minimize_bv_signed_with_config,
    ] {
        let result = optimize(&mut arena, &[], objective, &config).unwrap();
        assert!(
            matches!(result, OptOutcome::Unknown(reason) if reason.kind == UnknownKind::ResourceLimit)
        );
    }
}
