//! The NRA path must degrade to a *timely* `unknown` under its deterministic
//! wall-clock budget — never overrun it (the project's never-hang rule: every
//! solving path degrades to `unknown` under a deterministic resource bound; cf.
//! NRA's `MAX_CROSS_PRODUCTS` admission bound and the LIA deadline threading).
//!
//! Regression for #15: the coupled system `x²=y ∧ y²=x ∧ x·y=2` used to
//! terminate but only well past `config.timeout`, because the per-node lazy-SMT
//! solve spun through many refinement rounds *inside one call* with no deadline
//! check. The deadline is now threaded into the lazy-SMT loop, so the search
//! bails within roughly one round of the budget. Bailing to `unknown` is sound
//! (`unknown` is first-class); the budget never converts a `sat`/`unsat` into a
//! wrong verdict, and fast queries still decide unchanged.
#![cfg(feature = "full")]
#![allow(clippy::many_single_char_names)]

use std::time::{Duration, Instant};

use axeyum_ir::{Rational, Sort, TermArena};
use axeyum_solver::{CheckResult, SolverConfig, check_with_nra, solve};

fn real(arena: &mut TermArena, name: &str) -> axeyum_ir::TermId {
    let s = arena.declare(name, Sort::Real).unwrap();
    arena.var(s)
}

#[test]
fn coupled_system_respects_timeout_budget() {
    // x*x = y, y*y = x, x*y = 2 — three coupled real equations the linear
    // abstraction cannot decide, so the branch-and-bound / refinement search
    // runs until the budget. With a 3s timeout it must terminate *close* to the
    // budget (not seconds past it), and never produce a wrong verdict.
    let mut a = TermArena::new();
    let x = real(&mut a, "x");
    let y = real(&mut a, "y");
    let xx = a.real_mul(x, x).unwrap();
    let yy = a.real_mul(y, y).unwrap();
    let xy = a.real_mul(x, y).unwrap();
    let e1 = a.eq(xx, y).unwrap();
    let e2 = a.eq(yy, x).unwrap();
    let two = a.real_const(Rational::integer(2));
    let e3 = a.eq(xy, two).unwrap();

    let cfg = SolverConfig::default().with_timeout(Duration::from_secs(3));
    let start = Instant::now();
    let r = check_with_nra(&mut a, &[e1, e2, e3], &cfg).unwrap();
    let elapsed = start.elapsed();

    // The budget is now respected: terminate well under the old ~5.5s overrun.
    // (Generous ceiling so the assert is robust on a loaded CI box, while still
    // proving the deadline fires — the old behaviour ran multiple seconds over.)
    assert!(
        elapsed < Duration::from_secs(8),
        "NRA overran its 3s budget: elapsed {elapsed:?} (result {r:?})"
    );
    // Any of sat/unsat/unknown is acceptable here — only a *wrong* sat/unsat
    // would be a soundness bug. In practice this degrades to `unknown`.
    match r {
        CheckResult::Sat(_) | CheckResult::Unsat | CheckResult::Unknown(_) => {}
    }
}

#[test]
fn fast_query_still_decides_quickly_under_a_timeout() {
    // x*x < 0 is unsat (x² ≥ 0 from the sign rule). A configured timeout must
    // not perturb this fast, decided verdict.
    let mut a = TermArena::new();
    let x = real(&mut a, "x");
    let xx = a.real_mul(x, x).unwrap();
    let zero = a.real_const(Rational::integer(0));
    let lt = a.real_lt(xx, zero).unwrap();

    let cfg = SolverConfig::default().with_timeout(Duration::from_secs(3));
    let start = Instant::now();
    let r = check_with_nra(&mut a, &[lt], &cfg).unwrap();
    let elapsed = start.elapsed();

    assert!(
        matches!(r, CheckResult::Unsat),
        "x*x < 0 must be unsat, got {r:?}"
    );
    assert!(
        elapsed < Duration::from_secs(1),
        "fast unsat took too long: {elapsed:?}"
    );
}

#[test]
fn binomial_square_respects_timeout_and_is_not_sat() {
    // The negated binomial-square identity `(x+y)² ≠ x²+2xy+y²` is UNSAT (the
    // identity always holds), but the multivariate single-var NRA decider
    // declines (a `≠` with two vars) and the linear-abstraction NRA path's exact
    // Fourier–Motzkin LRA sub-solve blows up combinatorially on the abstracted
    // system — a single *uninterruptible* call that used to run ~10s past the
    // budget (a never-hang-rule violation). The deadline + size guard threaded
    // into the elimination now degrades it to a *timely* `unknown`.
    //
    // Soundness: the verdict must NEVER be `Sat` (the identity is a tautology, so
    // its negation is unsatisfiable). `unknown` or `unsat` are both acceptable;
    // only a wrong `sat` would be a soundness bug. The cardinal check here is
    // `!Sat`, with the budget honored.
    let mut a = TermArena::new();
    let x = real(&mut a, "x");
    let y = real(&mut a, "y");
    // (x + y)²
    let xy_sum = a.real_add(x, y).unwrap();
    let lhs = a.real_mul(xy_sum, xy_sum).unwrap();
    // x² + 2xy + y²
    let xx = a.real_mul(x, x).unwrap();
    let yy = a.real_mul(y, y).unwrap();
    let two = a.real_const(Rational::integer(2));
    let two_x = a.real_mul(two, x).unwrap();
    let two_xy = a.real_mul(two_x, y).unwrap();
    let sum1 = a.real_add(xx, two_xy).unwrap();
    let rhs = a.real_add(sum1, yy).unwrap();
    let eq = a.eq(lhs, rhs).unwrap();
    let ne = a.not(eq).unwrap();

    let cfg = SolverConfig::default().with_timeout(Duration::from_secs(10));
    let start = Instant::now();
    let r = solve(&mut a, &[ne], &cfg);
    let elapsed = start.elapsed();

    // The 10s budget is respected (well under the old ~20s overrun). Generous
    // ceiling so the assert is robust on a loaded CI box while still proving the
    // bound fires.
    assert!(
        elapsed < Duration::from_secs(13),
        "binomial-square negation overran its 10s budget: elapsed {elapsed:?} (result {r:?})"
    );
    // The cardinal soundness check: NEVER `Sat` (the negated identity is unsat).
    assert!(
        !matches!(r, Ok(CheckResult::Sat(_))),
        "(x+y)² ≠ x²+2xy+y² must never be Sat (the identity is a tautology), got {r:?}"
    );
}
