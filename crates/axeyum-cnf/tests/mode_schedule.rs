//! The stable/focused mode schedule, from outside the crate.
//!
//! # What these assert, and why it is not the verdict
//!
//! A mode switch is a search-order change. Every verdict-level gate — the
//! corpus sweep, `check_drat`, a differential fuzz — passes identically whether
//! the switch fires on the intended budget, fires on the wrong one, or never
//! fires at all, because none of them is a claim about the schedule. So these
//! tests assert the **schedule**: which mode, after how much work, on what
//! budget. Each one fails when the mechanism stops working, which is the only
//! reason to have it.
//!
//! # Two layers
//!
//! [`RestartPolicy`] is driven directly here with synthetic `(conflicts,
//! ticks)` inputs, because that is the only way to pin the interval arithmetic
//! exactly rather than approximately. The end-to-end assertions — that a real
//! search alternates, and that its schedule survives the clock changing under
//! it — live in `proof_sat.rs`'s unit tests, because
//! `solve_with_drat_proof_mode_traced` is not re-exported from `lib.rs` yet.
//! See this crate's `SearchPolicies::mode_switching` docs.
//!
//! # Reference
//!
//! `references/cadical/src/restart.cpp:18-84` (`Internal::stabilizing`) and
//! `:87-118` (`Internal::restarting`).

use axeyum_cnf::phase_policy::{
    MAX_RECORDED_MODE_TRANSITIONS, RestartConfig, RestartPolicy, RestartSchedule, SearchMode,
};
use axeyum_cnf::{CnfClause, CnfFormula, CnfLit, CnfVar, SearchPolicies, VecProofSink, check_drat};
use axeyum_cnf::{StreamingProofOutcome, solve_with_drat_proof_counted_with_policies};

/// Drives a policy to exhaustion against a synthetic work profile: `per_conflict`
/// ticks are charged for each of `conflicts` conflicts. Returns the mode entered
/// at each switch together with the tick total at which it happened.
fn run_schedule(
    mut policy: RestartPolicy,
    conflicts: u64,
    per_conflict: u64,
) -> Vec<(SearchMode, u64, u64)> {
    let mut switches = Vec::new();
    for conflict in 1..=conflicts {
        let ticks = conflict * per_conflict;
        if policy.should_switch(conflict, ticks) {
            let entered = policy.switch(conflict, ticks);
            switches.push((entered, conflict, ticks));
        }
    }
    switches
}

#[test]
fn the_default_policy_is_luby_everywhere_and_never_switches() {
    let policy = RestartPolicy::default();
    assert_eq!(policy.mode(), SearchMode::Focused);
    assert_eq!(policy.schedule(), RestartSchedule::Luby);
    assert!(!policy.needs_ticks());
    assert!(
        !policy.tracks_emas(),
        "the default search must execute no EMA arithmetic"
    );
    assert!(
        policy.rephase_allowed(),
        "with no mode schedule the rephase gate must be inert, not closed"
    );
    assert!(!policy.should_switch(u64::MAX, u64::MAX));
    assert!(run_schedule(RestartPolicy::default(), 100_000, 500).is_empty());
}

/// `RestartPolicy::ema` is the production setter the glue-EMA schedule never
/// had. Before it existed, `use_ema_restart` was a private field whose only
/// assignment of `true` in the whole crate was inside a `#[cfg(test)]` module.
#[test]
fn the_ema_schedule_is_selectable_without_switching() {
    let policy = RestartPolicy::ema();
    assert_eq!(policy.schedule(), RestartSchedule::Ema);
    assert!(policy.tracks_emas());
    assert!(
        !policy.needs_ticks(),
        "no switching, so no tick meter needed"
    );
    assert!(run_schedule(RestartPolicy::ema(), 100_000, 500).is_empty());
}

#[test]
fn mode_switching_starts_focused_and_alternates_strictly() {
    let policy = RestartPolicy::mode_switching();
    assert_eq!(
        policy.mode(),
        SearchMode::Focused,
        "the reference default-constructs `stable` to false"
    );
    assert_eq!(policy.schedule(), RestartSchedule::Ema);
    assert!(policy.needs_ticks());

    let switches = run_schedule(RestartPolicy::mode_switching(), 200_000, 7);
    assert!(switches.len() >= 6, "saw only {} switches", switches.len());
    let modes: Vec<SearchMode> = switches.iter().map(|(m, _, _)| *m).collect();
    for (i, mode) in modes.iter().enumerate() {
        let expected = if i % 2 == 0 {
            SearchMode::Stable
        } else {
            SearchMode::Focused
        };
        assert_eq!(
            *mode, expected,
            "switch {i} broke the alternation: {modes:?}"
        );
    }
}

/// The first interval is the conflict bootstrap; every later one is a tick
/// budget calibrated from what the first phase cost, growing as `stabphases^2`.
#[test]
fn the_intervals_are_the_references_bootstrap_then_quadratic_ticks() {
    let per_conflict = 10u64;
    let mut policy = RestartPolicy::mode_switching();
    let mut switches = Vec::new();
    for conflict in 1..=200_000u64 {
        let ticks = conflict * per_conflict;
        if policy.should_switch(conflict, ticks) {
            policy.switch(conflict, ticks);
            switches.push(conflict);
        }
    }
    let modes = policy.snapshot(200_000 * per_conflict);

    // Bootstrap: `stats.conflicts <= lim.stabilize` with `lim.stabilize` seeded
    // from `opts.stabilizeinit` (1e3), so the switch fires at 1001.
    assert_eq!(switches[0], 1_001);
    let unit = modes.transitions[0].budget_ticks;
    assert_eq!(
        unit,
        1_001 * per_conflict,
        "the increment must be the ticks the first phase actually paid"
    );

    // `next_delta_ticks = inc.stabilize * stabphases * stabphases`, with
    // `stabphases` read before the flip and advanced only on entry to stable.
    let budgets: Vec<u64> = modes
        .transitions
        .iter()
        .take(6)
        .map(|t| t.budget_ticks)
        .collect();
    assert_eq!(
        budgets,
        vec![unit, 4 * unit, 4 * unit, 9 * unit, 9 * unit, 16 * unit]
    );

    // Each phase runs for its budget, so the conflict gaps follow the same
    // shape once the bootstrap is past.
    let gaps: Vec<u64> = switches.windows(2).map(|w| w[1] - w[0]).collect();
    for w in gaps.windows(2) {
        assert!(w[1] >= w[0], "phases must not shrink: {gaps:?}");
    }
    assert!(
        gaps[3] > 3 * gaps[0],
        "growth must be superlinear: {gaps:?}"
    );
}

/// A mode's budget is against **its own** accumulated ticks, not the search
/// total (`lim.stabilize = stats.ticks.search[next_stable] + delta`). The
/// observable consequence: the two modes' tick shares track each other, rather
/// than the second mode being starved by everything the first already spent.
#[test]
fn each_mode_is_budgeted_against_its_own_tick_counter() {
    let per_conflict = 10u64;
    let total = 200_000u64;
    let mut policy = RestartPolicy::mode_switching();
    for conflict in 1..=total {
        let ticks = conflict * per_conflict;
        if policy.should_switch(conflict, ticks) {
            policy.switch(conflict, ticks);
        }
    }
    let modes = policy.snapshot(total * per_conflict);
    assert_eq!(
        modes.focused_ticks + modes.stable_ticks,
        total * per_conflict,
        "the split must partition the run"
    );
    let (lo, hi) = if modes.focused_ticks < modes.stable_ticks {
        (modes.focused_ticks, modes.stable_ticks)
    } else {
        (modes.stable_ticks, modes.focused_ticks)
    };
    assert!(
        hi < lo * 3,
        "neither mode may be starved: focused {} stable {}",
        modes.focused_ticks,
        modes.stable_ticks
    );
    assert_eq!(modes.stable_phases, modes.switches.div_ceil(2));
}

/// The schedule is a pure function of `(conflicts, ticks)`. Two policies fed the
/// same integer sequence produce the same schedule, and a policy fed a
/// *different* work profile produces a different one — so the equality above is
/// not vacuous.
#[test]
fn the_schedule_is_a_function_of_the_work_profile_alone() {
    let a = run_schedule(RestartPolicy::mode_switching(), 60_000, 10);
    let b = run_schedule(RestartPolicy::mode_switching(), 60_000, 10);
    assert_eq!(a, b);
    let c = run_schedule(RestartPolicy::mode_switching(), 60_000, 40);
    assert_ne!(
        a, c,
        "a four-times-heavier conflict must move the tick-denominated switches"
    );
}

/// `reset` restores a fresh schedule for the next incremental solve, and keeps
/// the configuration.
#[test]
fn reset_restores_the_opening_state() {
    let mut policy = RestartPolicy::mode_switching();
    for conflict in 1..=20_000u64 {
        let ticks = conflict * 10;
        if policy.should_switch(conflict, ticks) {
            policy.switch(conflict, ticks);
        }
    }
    assert!(policy.switches() > 0);
    policy.reset();
    assert_eq!(policy.switches(), 0);
    assert_eq!(policy.mode(), SearchMode::Focused);
    assert_eq!(policy.schedule(), RestartSchedule::Ema);
    assert!(policy.needs_ticks(), "reset must keep the configuration");
    assert_eq!(policy.snapshot(0).transitions, vec![]);
}

/// The transition log is capped, and says so rather than lying about the count.
#[test]
fn the_transition_log_is_capped_and_reports_truncation() {
    // A zero-conflict bootstrap makes the calibrated increment one tick, and a
    // quadratically rising work profile then outruns the quadratically rising
    // budgets — which is the only way to reach a 256-phase schedule inside a
    // test. It takes about 2,400 conflicts.
    let mut policy = RestartPolicy::new(RestartConfig {
        switching: true,
        focused: RestartSchedule::Ema,
        stable: RestartSchedule::Luby,
        bootstrap_conflicts: 0,
        rephase_in_stable_only: true,
    });
    let mut last_ticks = 0;
    for conflict in 1..=20_000u64 {
        last_ticks = conflict * conflict;
        if policy.should_switch(conflict, last_ticks) {
            policy.switch(conflict, last_ticks);
        }
    }
    let modes = policy.snapshot(last_ticks);
    assert!(modes.switches > MAX_RECORDED_MODE_TRANSITIONS as u64);
    assert_eq!(modes.transitions.len(), MAX_RECORDED_MODE_TRANSITIONS);
    assert!(modes.transitions_truncated);
}

/// The rephase gate: closed in focused mode only when a mode schedule is
/// running, and inert otherwise — gating on a stable mode that does not exist
/// would silently disable the rephase schedule rather than halve it.
#[test]
fn the_rephase_gate_is_inert_without_a_mode_schedule() {
    assert!(RestartPolicy::luby().rephase_allowed());
    assert!(RestartPolicy::ema().rephase_allowed());

    let mut switching = RestartPolicy::mode_switching();
    assert_eq!(switching.mode(), SearchMode::Focused);
    assert!(!switching.rephase_allowed(), "focused mode must refuse");
    switching.switch(1_001, 10_010);
    assert_eq!(switching.mode(), SearchMode::Stable);
    assert!(switching.rephase_allowed(), "stable mode must allow");

    let unconfined = RestartPolicy::new(RestartConfig {
        rephase_in_stable_only: false,
        ..RestartConfig {
            switching: true,
            focused: RestartSchedule::Ema,
            stable: RestartSchedule::Luby,
            ..RestartConfig::default()
        }
    });
    assert!(unconfined.rephase_allowed(), "opt-out must work");
}

fn lit(value: i64) -> CnfLit {
    let var = CnfVar::new(usize::try_from(value.abs()).unwrap() - 1).unwrap();
    let positive = CnfLit::positive(var);
    if value < 0 {
        positive.negated()
    } else {
        positive
    }
}

/// Pigeonhole: `pigeons` into `pigeons - 1` holes. Unsatisfiable and
/// exponentially hard for resolution, so a search over it analyses far more
/// conflicts than the bootstrap interval.
fn pigeonhole(pigeons: i64) -> CnfFormula {
    let holes = pigeons - 1;
    let v = |p: i64, h: i64| lit(holes * (p - 1) + h);
    let mut f = CnfFormula::new(usize::try_from(pigeons * holes).unwrap());
    for p in 1..=pigeons {
        f.add_clause(CnfClause::new(
            (1..=holes).map(|h| v(p, h)).collect::<Vec<_>>(),
        ))
        .unwrap();
    }
    for h in 1..=holes {
        for p1 in 1..=pigeons {
            for p2 in (p1 + 1)..=pigeons {
                f.add_clause(CnfClause::new(vec![v(p1, h).negated(), v(p2, h).negated()]))
                    .unwrap();
            }
        }
    }
    f
}

/// End to end through the crate's public surface: the policy really reaches the
/// search, the switches really happen, and the default really does not switch.
///
/// `mode_switches` is the summary the public `SearchCounters` carries; the full
/// schedule needs `solve_with_drat_proof_mode_traced`, which is not exported
/// yet.
#[test]
fn a_real_search_switches_modes_under_the_policy_and_not_under_the_default() {
    let f = pigeonhole(9);

    let mut sink = VecProofSink::new();
    let (_, baseline) = solve_with_drat_proof_counted_with_policies(
        &f,
        None,
        12_000,
        &mut sink,
        &SearchPolicies::default(),
    );
    assert!(
        baseline.conflicts > 5_000,
        "the fixture must reach the switching regime, saw {} conflicts",
        baseline.conflicts
    );
    assert_eq!(baseline.mode_switches, 0);
    assert_eq!(baseline.rephase_deferrals, 0);

    let mut sink = VecProofSink::new();
    let (_, switched) = solve_with_drat_proof_counted_with_policies(
        &f,
        None,
        12_000,
        &mut sink,
        &SearchPolicies::mode_switching(),
    );
    assert!(
        switched.mode_switches >= 4,
        "the mode schedule must fire, saw {} switches over {} conflicts and {} \
         ticks",
        switched.mode_switches,
        switched.conflicts,
        switched.ticks()
    );
}

/// Mode switching is verdict-preserving and certificate-preserving. It reorders
/// decisions and restarts; it must not change what the formula is, and the
/// `DRAT` stream it emits must still refute the original.
#[test]
fn mode_switching_preserves_the_verdict_and_the_proof() {
    let f = pigeonhole(6);
    for policies in [
        SearchPolicies::default(),
        SearchPolicies::ema_restart(),
        SearchPolicies::mode_switching(),
    ] {
        let mut sink = VecProofSink::new();
        let (outcome, counters) =
            solve_with_drat_proof_counted_with_policies(&f, None, 200_000, &mut sink, &policies);
        assert_eq!(
            outcome,
            StreamingProofOutcome::Unsat,
            "pigeonhole(6) is unsatisfiable under every policy"
        );
        assert_eq!(
            check_drat(&f, &sink.into_steps()),
            Ok(true),
            "the proof must check under {counters:?}"
        );
    }
}
