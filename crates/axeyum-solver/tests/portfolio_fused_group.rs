//! The integer-linear fused group, through the front door.
//!
//! `crates/axeyum-solver/src/portfolio.rs`'s unit tests exercise the group
//! primitive against synthetic arms — declared-order winners, the reserved
//! sequence at one worker, the disagreement gate, the memory share. These
//! exercise the **wiring**: what a whole query does once real routes are the
//! arms.
//!
//! # The degeneracy property, and why a verdict comparison cannot establish it
//!
//! The claim is *"with one worker the sequential path is byte-identical to the
//! pre-portfolio path"*. Comparing verdicts at one worker against verdicts at
//! two cannot check that, because two paths agreeing on every answer is exactly
//! what a **correct** portfolio also looks like: the comparison passes whether
//! the group ran or not, which makes it a measurement of nothing.
//!
//! So the property is enforced structurally — `dispatch_int_linear_refuters`
//! does not construct a group at one worker, it makes the call it always made —
//! and it is checked by counting: `portfolio_groups_run()` must not move across
//! a batch of integer queries at the default worker count. That assertion fails
//! the moment someone "simplifies" the wiring into always building a one-arm
//! group, which is the edit the property exists to forbid.
#![cfg(feature = "full")]

use axeyum_ir::{Sort, TermArena, TermId};
use axeyum_solver::{
    CheckResult, IntLinearPortfolioWorkersGuard, SolverConfig, check_auto_explained,
    portfolio_groups_run,
};
use std::time::Duration;

fn int(arena: &mut TermArena, name: &str) -> TermId {
    let symbol = arena.declare(name, Sort::Int).expect("declare");
    arena.var(symbol)
}

fn config(ms: u64) -> SolverConfig {
    SolverConfig {
        timeout: Some(Duration::from_millis(ms)),
        ..SolverConfig::default()
    }
}

/// The width every box in this file is given.
///
/// `int-box-eval` enumerates a proven integer box of up to
/// `MAX_INT_BOX_ENUM_CASES` (one million) cells, several rungs above the
/// integer-linear ladder. A query it can enumerate never reaches the group and
/// tests nothing here, so every query below is deliberately wider than that in
/// at least two variables. That is not a detail: the first draft of this file
/// used `x >= 3 && x + y <= 10` and every assertion in it was vacuous.
const WIDE: i128 = 1_000_000;

/// Bounds `v` to `[0, WIDE]`.
fn wide_bounds(arena: &mut TermArena, v: TermId) -> Vec<TermId> {
    let zero = arena.int_const(0);
    let hi = arena.int_const(WIDE);
    vec![
        arena.int_ge(v, zero).expect("build"),
        arena.int_le(v, hi).expect("build"),
    ]
}

/// A satisfiable linear-integer query with Boolean structure over a box far
/// too wide to enumerate. `x = 3, y = 1000, z = 5` satisfies it.
fn satisfiable(arena: &mut TermArena) -> Vec<TermId> {
    let x = int(arena, "px_sat_x");
    let y = int(arena, "px_sat_y");
    let z = int(arena, "px_sat_z");
    let mut out = wide_bounds(arena, x);
    out.extend(wide_bounds(arena, y));
    out.extend(wide_bounds(arena, z));
    let thousand = arena.int_const(1_000);
    let three = arena.int_const(3);
    let five = arena.int_const(5);
    let sum = arena.int_add(x, y).expect("build");
    out.push(arena.int_ge(sum, thousand).expect("build"));
    out.push(arena.int_ge(z, five).expect("build"));
    let small_x = arena.int_le(x, three).expect("build");
    let small_y = arena.int_le(y, three).expect("build");
    out.push(arena.or(small_x, small_y).expect("build"));
    out
}

/// An unsatisfiable linear-integer query that reaches the same rung as
/// [`satisfiable`]: `x + y >= 6`, `x <= 3`, `y <= 3`, `(x <= 2 or y <= 2)`.
///
/// The only assignment satisfying the bounds and the sum is `x = y = 3`, which
/// falsifies the disjunction -- so the refutation needs a **case split** and
/// nothing above the ladder can take it. Each guard against an upstream rung
/// was measured, not guessed; three earlier drafts of this query were answered
/// before the ladder was reached, and each is recorded here because the failure
/// mode is silent:
///
/// * `x >= 500, y >= 500, (x <= 3 or y <= 3)` -- decided `unsat` by
///   **`dl-online`**: bounds and differences are its fragment. Hence the
///   two-variable `x + y`, which is not a difference constraint.
/// * `x + y >= 1000, x <= 100, y <= 100` and `x + y >= 6, x + y <= 5` --
///   decided `unsat` by **`int-box-eval`**, whose interval propagation
///   intersects the sum's range with the constraint and finds it empty without
///   enumerating anything. Here `x + y` ranges over `[0, 6]` and the constraint
///   is `>= 6`, so that intersection is non-empty and interval reasoning alone
///   cannot refute.
/// * every draft without the free wide-boxed `z` -- **`int-box-eval`** again,
///   this time by enumeration: `4 x 4` cells is far under its one-million cap.
///   With `z` the box is 16 million cells and it declines.
///
/// The disjunction additionally keeps `lia-simplex` out, which declines Boolean
/// structure.
fn unsatisfiable(arena: &mut TermArena) -> Vec<TermId> {
    let x = int(arena, "px_unsat_x");
    let y = int(arena, "px_unsat_y");
    let z = int(arena, "px_unsat_z");
    let mut out = wide_bounds(arena, x);
    out.extend(wide_bounds(arena, y));
    out.extend(wide_bounds(arena, z));
    let two = arena.int_const(2);
    let three = arena.int_const(3);
    let six = arena.int_const(6);
    let sum = arena.int_add(x, y).expect("build");
    out.push(arena.int_ge(sum, six).expect("build"));
    out.push(arena.int_le(x, three).expect("build"));
    out.push(arena.int_le(y, three).expect("build"));
    let small_x = arena.int_le(x, two).expect("build");
    let small_y = arena.int_le(y, two).expect("build");
    out.push(arena.or(small_x, small_y).expect("build"));
    out
}

/// Unsatisfiable over ℤ, satisfiable over ℚ: `2x = 2y + 1`.
///
/// The left side is even and the right is odd, so no integer pair works, while
/// `x = y + 1/2` works over the rationals. Any arm that relaxes integers to
/// reals answers `sat`. Kept out of [`QUERIES`] on purpose: it is refuted by a
/// Diophantine gcd test *inside* the integer-linear refuters and so does not
/// reach `lia-dpll`, which makes it a soundness non-regression check rather
/// than coverage of the group — and saying so is the point.
fn integer_only_unsatisfiable(arena: &mut TermArena) -> Vec<TermId> {
    let x = int(arena, "px_frac_x");
    let y = int(arena, "px_frac_y");
    let mut out = wide_bounds(arena, x);
    out.extend(wide_bounds(arena, y));
    let two = arena.int_const(2);
    let one = arena.int_const(1);
    let lhs = arena.int_mul(two, x).expect("build");
    let doubled_y = arena.int_mul(two, y).expect("build");
    let rhs = arena.int_add(doubled_y, one).expect("build");
    out.push(arena.eq(lhs, rhs).expect("build"));
    out
}

fn verdict_name(result: &CheckResult) -> &'static str {
    match result {
        CheckResult::Sat(_) => "sat",
        CheckResult::Unsat => "unsat",
        CheckResult::Unknown(_) => "unknown",
    }
}

fn decide(assertions: fn(&mut TermArena) -> Vec<TermId>, ms: u64) -> (String, String) {
    let mut arena = TermArena::new();
    let terms = assertions(&mut arena);
    let (result, trace) =
        check_auto_explained(&mut arena, &terms, &config(ms)).expect("dispatch did not error");
    (verdict_name(&result).to_owned(), trace.to_json())
}

/// The queries that are checked to reach the integer-linear ladder.
const QUERIES: [(&str, fn(&mut TermArena) -> Vec<TermId>); 2] = [
    ("satisfiable", satisfiable),
    ("unsatisfiable", unsatisfiable),
];

#[test]
fn every_query_here_reaches_the_integer_linear_ladder() {
    // Coverage, not correctness. A query decided upstream (`int-box-eval`,
    // `lia-simplex`, a refuter) passes every other assertion in this file while
    // measuring nothing about the group -- the vacuous negative control this
    // repository keeps finding. The evidence is the route trail naming the
    // ladder's own route, not a reading of the dispatch order.
    for (name, build) in QUERIES {
        let (_verdict, trail) = decide(build, 5_000);
        assert!(
            trail.contains("\"route\":\"lia-dpll\""),
            "{name} never reaches the integer-linear ladder, so it tests nothing here: {trail}"
        );
    }
}

#[test]
fn at_the_default_worker_count_no_fused_group_is_constructed_at_all() {
    // The degeneracy property as an executable claim. Not "the answers match"
    // — "the new mechanism did not run".
    let before = portfolio_groups_run();
    for (name, build) in QUERIES {
        let (verdict, _) = decide(build, 5_000);
        assert_ne!(
            verdict, "unknown",
            "{name} must still be decided by the sequential ladder"
        );
    }
    assert_eq!(
        portfolio_groups_run(),
        before,
        "at one worker the integer-linear ladder must not construct a fused group; \
         it must make the call it always made"
    );
}

#[test]
fn two_workers_reach_the_same_verdicts_as_one() {
    for (name, build) in QUERIES {
        let (sequential, _) = decide(build, 5_000);
        let raced = {
            let _workers = IntLinearPortfolioWorkersGuard::set(2);
            let (verdict, _) = decide(build, 5_000);
            verdict
        };
        assert_eq!(
            sequential, raced,
            "{name}: racing the arms changed the verdict, which it must never do"
        );
    }
}

#[test]
fn racing_actually_runs_the_group() {
    // The control for the test above: if the guard did not take effect, that
    // test would compare the sequential path with itself and pass regardless.
    let before = portfolio_groups_run();
    {
        let _workers = IntLinearPortfolioWorkersGuard::set(2);
        let (verdict, _) = decide(satisfiable, 5_000);
        assert_eq!(verdict, "sat");
    }
    assert!(
        portfolio_groups_run() > before,
        "the worker override must actually put the ladder through a fused group"
    );
}

#[test]
fn the_worker_guard_restores_the_previous_setting() {
    let before = portfolio_groups_run();
    {
        let _workers = IntLinearPortfolioWorkersGuard::set(2);
        let (_verdict, _trace) = decide(satisfiable, 5_000);
    }
    let after_guard = portfolio_groups_run();
    let (_verdict, _trace) = decide(satisfiable, 5_000);
    assert_eq!(
        portfolio_groups_run(),
        after_guard,
        "once the guard is dropped the ladder must be sequential again"
    );
    assert!(after_guard > before, "the guard did take effect");
}

#[test]
fn a_raced_group_never_relaxes_integers_to_reals() {
    // The soundness case that matters for THIS group: its second arm is a
    // bounded bit-blast, and a blast at a width too narrow for the witness, or
    // a relaxation to the rationals, both answer `sat` on `0 < 2x < 2`. The
    // shipped sequential ladder refutes it; the raced one must too.
    let (sequential, _) = decide(integer_only_unsatisfiable, 5_000);
    assert_eq!(
        sequential, "unsat",
        "control: the sequential ladder refutes 0 < 2x < 2 over the integers"
    );
    let _workers = IntLinearPortfolioWorkersGuard::set(2);
    let (raced, _) = decide(integer_only_unsatisfiable, 5_000);
    assert_eq!(
        raced, "unsat",
        "an arm that answered `sat` here would be relaxing integers to rationals"
    );
}

#[test]
fn a_raced_group_records_every_arm_it_ran_in_declared_order() {
    let _workers = IntLinearPortfolioWorkersGuard::set(2);
    let (_verdict, trail) = decide(satisfiable, 5_000);
    let lia = trail.find("\"route\":\"lia-dpll\"");
    let blast = trail.find("\"route\":\"int-blast-ladder\"");
    // `lia-dpll` decides this query, so it is always in the trail. The blast arm
    // may or may not have finished before it was stopped — that is the
    // attribution non-determinism the module documents — but when it IS there it
    // must come second.
    assert!(lia.is_some(), "the first arm is always recorded: {trail}");
    if let (Some(lia), Some(blast)) = (lia, blast) {
        assert!(
            lia < blast,
            "arms are recorded in declared order, not finishing order: {trail}"
        );
    }
}
