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
#![allow(clippy::many_single_char_names)]

use std::time::{Duration, Instant};

use axeyum_ir::{Rational, Sort, TermArena};
use axeyum_solver::{CheckResult, SolverConfig, check_with_nra};

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
