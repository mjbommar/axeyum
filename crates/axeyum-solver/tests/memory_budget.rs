//! `SolverConfig::memory_limit_mb` as a consumer sees it.
//!
//! Deliberately **not** `#![cfg(feature = "full")]`: the defect this covers was
//! that the field is inert on the *default* build, so a suite that only runs
//! under `full` would be testing the wrong configuration. This runs in a plain
//! `cargo test --workspace`.
//!
//! The unit tests in `src/memory_budget.rs` cover the mechanism. What is here
//! and cannot be there is the **differential**: a budget must change *whether*
//! a query is decided, never *what* it is decided to be. A guard that quietly
//! flipped a `sat` to an `unsat` would be far worse than the inert field it
//! replaced.

use axeyum_ir::{TermArena, TermId};
use axeyum_solver::{CheckResult, SatBvBackend, SolverBackend, SolverConfig, UnknownKind};

/// A generous cap: 1 TiB, past anything these queries encode.
const GENEROUS_MB: u64 = 1 << 20;
/// 1 MiB buys ~2730 clauses at the module's charge rate. Every query below
/// encodes past that.
const TINY_MB: u64 = 1;

fn verdict(arena: &TermArena, assertions: &[TermId], config: &SolverConfig) -> CheckResult {
    SatBvBackend::new()
        .check(arena, assertions, config)
        .expect("the pure-Rust backend decides or declines, never errors here")
}

/// `(name, arena, assertions)` for a handful of shapes with known, differing
/// verdicts — one `sat`, one `unsat`, so a guard that collapsed every answer to
/// one of them would be caught.
fn corpus() -> Vec<(&'static str, TermArena, Vec<TermId>)> {
    let mut out = Vec::new();

    // Both shapes are WIDE rather than hard: they must encode past the ~2730
    // clauses a 1 MiB budget buys, while still being decided in milliseconds so
    // this suite stays runnable in a default `cargo test`. A multiplier miter
    // does the first but not the second (a 24-bit one did not finish in 10 min
    // in debug), which is the wrong trade for a guard test.
    {
        let mut arena = TermArena::new();
        let x = arena.bv_var("x", 512).unwrap();
        let y = arena.bv_var("y", 512).unwrap();
        let sum = arena.bv_add(x, y).unwrap();
        let target = arena.bv_const(512, 5).unwrap();
        let two = arena.bv_const(512, 2).unwrap();
        let sum_is_target = arena.eq(sum, target).unwrap();
        let x_is_two = arena.eq(x, two).unwrap();
        out.push((
            "512-bit sum hits a target",
            arena,
            vec![sum_is_target, x_is_two],
        ));
    }

    {
        // `x + y != y + x` is unsatisfiable, and an adder miter is easy for CDCL.
        let mut arena = TermArena::new();
        let x = arena.bv_var("x", 512).unwrap();
        let y = arena.bv_var("y", 512).unwrap();
        let left = arena.bv_add(x, y).unwrap();
        let right = arena.bv_add(y, x).unwrap();
        let equal = arena.eq(left, right).unwrap();
        let assertion = arena.not(equal).unwrap();
        out.push(("512-bit addition commutes", arena, vec![assertion]));
    }

    out
}

/// The property that matters: a budget generous enough not to bind must leave
/// the verdict **identical** to having no budget at all.
///
/// This is the differential a soundness bug in the guard would fail. It is also
/// why the corpus carries both a `sat` and an `unsat`: a guard that returned
/// `Unknown` for everything would pass a one-sided version of this test.
#[test]
fn a_generous_budget_never_changes_a_verdict() {
    let mut saw_sat = false;
    let mut saw_unsat = false;
    for (name, arena, assertions) in corpus() {
        let unbounded = verdict(&arena, &assertions, &SolverConfig::default());
        let bounded = verdict(
            &arena,
            &assertions,
            &SolverConfig::default().with_memory_limit_mb(GENEROUS_MB),
        );
        let same = matches!(
            (&unbounded, &bounded),
            (CheckResult::Sat(_), CheckResult::Sat(_))
                | (CheckResult::Unsat, CheckResult::Unsat)
                | (CheckResult::Unknown(_), CheckResult::Unknown(_))
        );
        assert!(
            same,
            "{name}: a non-binding memory budget changed the verdict \
             ({unbounded:?} -> {bounded:?})"
        );
        saw_sat |= matches!(unbounded, CheckResult::Sat(_));
        saw_unsat |= matches!(unbounded, CheckResult::Unsat);
    }
    // Without this the test passes on a corpus that is decided `unknown`
    // throughout, which is exactly the vacuous shape CLAUDE.md warns about.
    assert!(
        saw_sat && saw_unsat,
        "the corpus must exercise both directions (sat={saw_sat}, unsat={saw_unsat})"
    );
}

/// A budget too small for the encoding must decline, and say `MemoryLimit`.
///
/// Before 2026-08-21 this was the whole defect: the same call returned a
/// verdict, having silently ignored the cap, on every non-`z3` build.
#[test]
fn a_budget_smaller_than_the_encoding_declines_as_a_memory_limit() {
    for (name, arena, assertions) in corpus() {
        let result = verdict(
            &arena,
            &assertions,
            &SolverConfig::default().with_memory_limit_mb(TINY_MB),
        );
        let CheckResult::Unknown(reason) = result else {
            panic!("{name}: a {TINY_MB} MiB budget must not decide this: {result:?}");
        };
        assert_eq!(
            reason.kind,
            UnknownKind::MemoryLimit,
            "{name}: declining for memory must be classified as memory, not as \
             {:?} — a consumer reacts differently to the two",
            reason.kind
        );
        assert!(
            reason.detail.contains("memory_limit_mb"),
            "{name}: the reason must name the budget: {}",
            reason.detail
        );
    }
}

/// The default configuration sets no budget, so nothing here may cost it a
/// verdict. Cheap, but it is the regression that a too-eager default would
/// cause, and it would look like a solver capability loss rather than a config
/// change.
#[test]
fn no_budget_is_still_no_budget() {
    assert!(SolverConfig::default().memory_limit_mb.is_none());
    for (name, arena, assertions) in corpus() {
        let result = verdict(&arena, &assertions, &SolverConfig::default());
        assert!(
            matches!(result, CheckResult::Sat(_) | CheckResult::Unsat),
            "{name}: the default configuration must still decide this: {result:?}"
        );
    }
}
