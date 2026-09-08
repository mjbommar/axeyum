//! Controls for the integer-route counters.
//!
//! The failure this suite exists to prevent is **not** "a counter is off by
//! one". It is the one the `QF_LRA` lane recorded: a counter struct wired into
//! the reporting path while the engine underneath never increments it, so a
//! diagnostic prints `0` for two days and looks healthy because the fields
//! around it are real. Every test below therefore drives a **real query** and
//! requires the sites to have fired; none of them constructs a
//! [`super::LiaCounters`] by hand and asserts about it.
//!
//! One exception, and it is about a different kind of claim:
//! `every_group_is_representable_in_the_policy` asserts about the POLICY type,
//! not about a counter. "Can this group be switched off" cannot be asked by
//! driving a query — a query can only show that a group WAS collected — so that
//! test builds the two extreme snapshots directly. It proves nothing about
//! whether any site increments, and is not evidence that any group is wired.

use super::{
    GroupReading, LiaCounterGroup, LiaCounterPolicy, LiaCounters, LiaCountersGuard,
    last_lia_counters,
};
use crate::backend::{CheckResult, SolverConfig};
use axeyum_ir::{Sort, TermArena, TermId};

fn ivar(arena: &mut TermArena, name: &str) -> TermId {
    let symbol = arena.declare(name, Sort::Int).expect("declare int");
    arena.var(symbol)
}

fn iconst(arena: &mut TermArena, n: i128) -> TermId {
    arena.int_const(n)
}

/// A satisfiable query the online integer theory has to *search*: two
/// disjunctions and two bounds, so the driver decides, propagates and asserts
/// repeatedly instead of answering from the first assert.
fn searching_query() -> (TermArena, Vec<TermId>) {
    let mut arena = TermArena::new();
    let x = ivar(&mut arena, "x");
    let y = ivar(&mut arena, "y");
    let zero = iconst(&mut arena, 0);
    let three = iconst(&mut arena, 3);
    let five = iconst(&mut arena, 5);
    let nine = iconst(&mut arena, 9);

    let x_pos = arena.int_gt(x, zero).expect("x > 0");
    let x_big = arena.int_gt(x, three).expect("x > 3");
    let x_cap = arena.int_lt(x, five).expect("x < 5");
    let y_gt_x = arena.int_gt(y, x).expect("y > x");
    let y_big = arena.int_gt(y, three).expect("y > 3");
    let y_cap = arena.int_lt(y, nine).expect("y < 9");

    let split_x = arena.or(x_pos, x_big).expect("x disjunction");
    let split_y = arena.or(y_gt_x, y_big).expect("y disjunction");
    (arena, vec![split_x, x_cap, split_y, y_cap])
}

/// An integer-infeasible conjunction whose **rational** relaxation is feasible
/// at a fractional point, so the warm filter declines and the offline decider —
/// tightening, Gomory, branch-and-bound — is the thing that answers.
fn parity_query() -> (TermArena, Vec<TermId>) {
    let mut arena = TermArena::new();
    let x = ivar(&mut arena, "x");
    let y = ivar(&mut arena, "y");
    let one = iconst(&mut arena, 1);
    let two = iconst(&mut arena, 2);
    let two_x = arena.int_mul(two, x).expect("2x");
    let two_y = arena.int_mul(two, y).expect("2y");
    let odd = arena.int_add(two_y, one).expect("2y + 1");
    let parity = arena.eq(two_x, odd).expect("2x = 2y + 1");
    (arena, vec![parity])
}

/// A pure conjunction, which the offline decider takes on its own.
fn conjunctive_query() -> (TermArena, Vec<TermId>) {
    let mut arena = TermArena::new();
    let var_x = ivar(&mut arena, "x");
    let var_y = ivar(&mut arena, "y");
    let zero = iconst(&mut arena, 0);
    let ten = iconst(&mut arena, 10);
    let x_pos = arena.int_lt(zero, var_x).expect("0 < x");
    let ordered = arena.int_lt(var_x, var_y).expect("x < y");
    let y_cap = arena.int_lt(var_y, ten).expect("y < 10");
    (arena, vec![x_pos, ordered, y_cap])
}

/// Every [`LiaCounterGroup`] must be representable in [`LiaCounterPolicy`], and
/// switchable independently.
///
/// This is what earns the `#[allow(clippy::struct_excessive_bools)]` on the two
/// policy structs. The lint's premise is that interchangeable bools get mixed
/// up; the answer here is that each one IS a group, so adding a group without
/// its switch fails this test rather than silently leaving a group that can
/// never be turned off.
///
/// The one test in this file that builds a snapshot by hand — see the module
/// doc for why that is the only way to ask this question, and for what it
/// therefore does NOT show.
#[test]
fn every_group_is_representable_in_the_policy() {
    let groups = [
        LiaCounterGroup::Offline,
        LiaCounterGroup::Theory,
        LiaCounterGroup::Propagation,
        LiaCounterGroup::Warm,
    ];
    let on = LiaCounters {
        groups: LiaCounterPolicy::ALL.into(),
        ..LiaCounters::default()
    };
    let off = LiaCounters {
        groups: LiaCounterPolicy::NONE.into(),
        ..LiaCounters::default()
    };
    for group in groups {
        assert_ne!(
            on.group_reading(group),
            GroupReading::NotCollected,
            "{group:?} is not switched ON by LiaCounterPolicy::ALL"
        );
        assert_eq!(
            off.group_reading(group),
            GroupReading::NotCollected,
            "{group:?} is not switched OFF by LiaCounterPolicy::NONE"
        );
    }
}

#[test]
fn a_thread_that_never_enabled_collection_reads_none_not_zero() {
    // The whole reason `last_lia_counters` returns an `Option`. An all-zero
    // struct here would be indistinguishable from "the integer routes did
    // nothing", which is the confident-zero failure this module is built
    // against. libtest gives each test its own thread, so this observes a
    // never-armed thread.
    let (arena, assertions) = conjunctive_query();
    let _ = crate::lra::check_with_lia_simplex(&arena, &assertions).expect("decided");
    assert!(
        last_lia_counters().is_none(),
        "unarmed thread must report None, never a zeroed snapshot"
    );
}

#[test]
fn every_group_is_incremented_by_a_real_online_query() {
    // The anti-false-zero control. If the recording sites are removed from
    // `lra.rs` / `lia_online.rs` and only the struct survives, this is the test
    // that dies — each group's `Measured` reading requires its entry counter to
    // have been incremented by code that actually ran.
    //
    // Two queries under one guard, because no single small query reaches every
    // site: a search that never refutes drives propagation but leaves the
    // offline decider alone, and a conjunction the warm filter refutes outright
    // never clones an arena. The claim being pinned is "every documented
    // recording site fires in production code", not "one query touches them
    // all".
    let guard = LiaCountersGuard::enable();
    let (arena, assertions) = searching_query();
    let searched = crate::lia_online::check_qf_lia_online(&arena, &assertions, &default_config())
        .expect("decidable");
    let (arena, assertions) = parity_query();
    let refuted = crate::lia_online::check_qf_lia_online(&arena, &assertions, &default_config())
        .expect("decidable");
    drop(guard);
    assert!(
        matches!(searched, CheckResult::Sat(_)),
        "the searching query is satisfiable; got {searched:?}"
    );
    assert!(
        matches!(refuted, CheckResult::Unsat),
        "2x = 2y + 1 has no integer solution; got {refuted:?}"
    );

    let counters = last_lia_counters().expect("guard was armed");
    for group in [
        LiaCounterGroup::Offline,
        LiaCounterGroup::Theory,
        LiaCounterGroup::Propagation,
    ] {
        assert_eq!(
            counters.group_reading(group),
            GroupReading::Measured,
            "group {group:?} never ran on a query that drives the whole online \
             integer route; counters: {counters:?}"
        );
    }

    // Each group's substance, not just its entry counter — an entry counter can
    // be incremented by a wrapper that then forwards to an uninstrumented body.
    assert!(
        counters.simplex_solves > 0,
        "the exact-rational simplex ran but reported no solve: {counters:?}"
    );
    assert!(
        counters.gomory_calls > 0 && counters.gomory_rounds > 0,
        "the cut engine runs ahead of branch-and-bound on every offline call \
         with a buildable tableau, and reported nothing: {counters:?}"
    );
    assert!(
        counters.gomory_rows > 0 && counters.gomory_columns > 0,
        "a built Gomory tableau has a shape, and `gomory_pivots` is unreadable \
         without it: {counters:?}"
    );
    assert!(
        counters.theory_feasibility_checks > 0,
        "asserts happened but no feasibility check was counted: {counters:?}"
    );
    // The clone counter is kept, and what it must now report is ZERO on the
    // feasibility path: every polarity term is pre-built at construction, so a
    // check assembles its conjunction against `&self.arena`. Before that, the
    // committed 27-file `QF_LIA` loss list copied 352 million term nodes
    // through here. A nonzero value means a clone came back — which is the
    // regression, not the measurement failing.
    assert_eq!(
        counters.arena_clones, 0,
        "the feasibility path must not clone the arena: {counters:?}"
    );
    assert_eq!(counters.arena_clone_nodes, 0, "{counters:?}");
    assert!(
        counters.filter_refuted + counters.filter_integral + counters.filter_inconclusive > 0,
        "every feasibility check over a non-empty live set consults the warm \
         filter, so one of its three verdicts must have been counted: \
         {counters:?}"
    );
    assert!(
        counters.propagate_atoms_scanned > 0,
        "propagation ran but scanned no atoms: {counters:?}"
    );
}

#[test]
fn the_offline_decider_reports_which_engine_ran() {
    // `bnb_nodes` is not incremented per node — it is `node_cap - budget` at the
    // top-level return, which is what keeps arming the guard from changing the
    // search's shape. This pins that the delta is actually read.
    let mut arena = TermArena::new();
    let x = ivar(&mut arena, "x");
    let two = iconst(&mut arena, 2);
    let six = iconst(&mut arena, 6);
    let twice = arena.int_mul(two, x).expect("2*x");
    // 2x > 2 ∧ 2x < 6 — a fractional-vertex polytope over the rationals.
    let lo = arena.int_gt(twice, two).expect("2x > 2");
    let hi = arena.int_lt(twice, six).expect("2x < 6");

    let guard = LiaCountersGuard::enable();
    let verdict = crate::lra::check_with_lia_simplex(&arena, &[lo, hi]).expect("decided");
    drop(guard);
    assert!(matches!(verdict, CheckResult::Sat(_)), "got {verdict:?}");

    let counters = last_lia_counters().expect("armed");
    assert_eq!(
        counters.group_reading(LiaCounterGroup::Offline),
        GroupReading::Measured,
        "the offline decider ran: {counters:?}"
    );
    // Gomory may decide this outright, in which case branch-and-bound never
    // runs. Either way exactly one of the two engines must have been counted —
    // an all-zero offline group past the entry counter would mean neither site
    // fired, which is the defect this suite is for.
    assert!(
        counters.bnb_roots > 0 || counters.gomory_calls > 0,
        "the offline decider entered but neither engine was counted: {counters:?}"
    );
    if counters.bnb_roots > 0 {
        assert!(
            counters.bnb_nodes >= counters.bnb_roots,
            "every branch-and-bound run explores at least its root node: {counters:?}"
        );
    }
}

#[test]
fn the_clone_counter_still_fires_on_the_path_that_still_clones() {
    // Paired with `every_group_is_incremented_by_a_real_online_query`, which
    // now requires `arena_clones == 0` on the feasibility path. That assertion
    // alone would go on passing if `record_arena_clone` were deleted outright,
    // so the counter needs a live positive control: one call through the
    // owned-arena builder that the equality-branch probe still needs, and the
    // node total must be the arena's real size, not a placeholder.
    let mut arena = TermArena::new();
    let x = ivar(&mut arena, "x");
    let zero = iconst(&mut arena, 0);
    let atom = arena.int_lt(zero, x).expect("0 < x");
    let mut theory = crate::lia_online::LiaTheory::new(&arena, &[atom]);
    crate::euf_egraph::TheorySolver::assert(&mut theory, 0, false)
        .expect("`x <= 0` alone is feasible");

    let guard = LiaCountersGuard::enable();
    let (cloned, terms) = theory
        .terms_for(&theory.live_literals())
        .expect("terms build");
    drop(guard);
    assert_eq!(terms.len(), 1);

    let counters = last_lia_counters().expect("armed");
    assert_eq!(counters.arena_clones, 1, "{counters:?}");
    assert_eq!(
        counters.arena_clone_nodes,
        cloned.len() as u64,
        "the node total must be the arena's real size: {counters:?}"
    );
}

#[test]
fn the_cut_engines_own_pivots_are_counted_separately_from_the_simplexs() {
    // The counter this test exists for was MISSING when the instrumentation
    // first landed, and its absence was not neutral. On
    // `BART-PT-020/RF-13.smt2` the sweep reported `simplex_pivots=0` against
    // 10,102 Gomory calls — which reads as "no pivoting happened" when in fact
    // every pivot had moved into the cut engine, where nothing was watching.
    // A conjunction whose standard form is infeasible at the origin forces at
    // least one Gomory pivot; `simplex_pivots` stays a separate number.
    let (arena, assertions) = conjunctive_query();
    let guard = LiaCountersGuard::enable();
    let verdict = crate::lra::check_with_lia_simplex(&arena, &assertions).expect("decided");
    drop(guard);
    assert!(matches!(verdict, CheckResult::Sat(_)), "got {verdict:?}");

    let counters = last_lia_counters().expect("armed");
    assert!(
        counters.gomory_pivots > 0,
        "the cut engine reached a feasible vertex from an origin its own \
         constraints exclude, so it pivoted: {counters:?}"
    );
}

#[test]
fn the_simplex_records_the_shape_of_the_system_it_was_handed() {
    // `simplex_rows` / `simplex_columns` exist to price one pivot as
    // `O(rows × columns)`. A constant, or the wrong system's dimensions, would
    // make every such price wrong while still looking measured — so this pins
    // them against a system whose size is known exactly. The LP relaxation
    // probe is the deterministic way in: one solve, one collected constraint
    // per assertion, no branching.
    let mut arena = TermArena::new();
    let var_x = ivar(&mut arena, "x");
    let var_y = ivar(&mut arena, "y");
    let zero = iconst(&mut arena, 0);
    let ten = iconst(&mut arena, 10);
    let x_pos = arena.int_lt(zero, var_x).expect("0 < x");
    let ordered = arena.int_lt(var_x, var_y).expect("x < y");
    let y_cap = arena.int_lt(var_y, ten).expect("y < 10");

    let guard = LiaCountersGuard::enable();
    let relaxation = crate::lra::lp_relaxation_feasibility(&arena, &[x_pos, ordered, y_cap]);
    drop(guard);
    assert_eq!(relaxation, crate::lra::LpRelaxation::Feasible);

    let counters = last_lia_counters().expect("armed");
    assert_eq!(counters.lp_relaxation_calls, 1, "{counters:?}");
    assert_eq!(counters.simplex_solves, 1, "{counters:?}");
    assert_eq!(
        counters.simplex_rows, 3,
        "one row per collected constraint: {counters:?}"
    );
    assert_eq!(
        counters.simplex_columns, 5,
        "two problem variables plus one slack per row: {counters:?}"
    );
}

#[test]
fn a_group_the_policy_switched_off_reads_not_collected() {
    // `NotCollected` and `NotReached` are the two ways a group can be all-zero
    // and mean different things. A report that cannot tell them apart is the
    // confident zero in a different costume.
    let (arena, assertions) = parity_query();
    let guard = LiaCountersGuard::enable_with(LiaCounterPolicy::OFFLINE_ONLY);
    let _ = crate::lia_online::check_qf_lia_online(&arena, &assertions, &default_config())
        .expect("decidable");
    drop(guard);

    let counters = last_lia_counters().expect("armed");
    assert_eq!(
        counters.group_reading(LiaCounterGroup::Offline),
        GroupReading::Measured
    );
    assert_eq!(
        counters.group_reading(LiaCounterGroup::Theory),
        GroupReading::NotCollected,
        "the theory ran; its zeros are structural, not measured: {counters:?}"
    );
    assert_eq!(
        counters.group_reading(LiaCounterGroup::Propagation),
        GroupReading::NotCollected
    );
    assert_eq!(
        counters.theory_asserts, 0,
        "a switched-off group must not be written to at all"
    );
}

#[test]
fn a_collected_group_that_never_ran_reads_not_reached() {
    // The third case: collection on, code never executed. A conjunctive query
    // handed straight to the offline route never touches the online theory.
    let (arena, assertions) = conjunctive_query();
    let guard = LiaCountersGuard::enable();
    let _ = crate::lra::check_with_lia_simplex(&arena, &assertions).expect("decided");
    drop(guard);

    let counters = last_lia_counters().expect("armed");
    assert_eq!(
        counters.group_reading(LiaCounterGroup::Offline),
        GroupReading::Measured
    );
    assert_eq!(
        counters.group_reading(LiaCounterGroup::Theory),
        GroupReading::NotReached,
        "the online theory was collected but never entered: {counters:?}"
    );
}

#[test]
fn the_guard_restores_the_previous_policy_on_drop() {
    let (arena, assertions) = conjunctive_query();
    let outer = LiaCountersGuard::enable_with(LiaCounterPolicy::OFFLINE_ONLY);
    {
        let _inner = LiaCountersGuard::enable_with(LiaCounterPolicy::NONE);
        let _ = crate::lra::check_with_lia_simplex(&arena, &assertions).expect("decided");
        let inner_counters = last_lia_counters().expect("armed");
        assert_eq!(
            inner_counters.offline_calls, 0,
            "NONE collects nothing: {inner_counters:?}"
        );
    }
    // Back under the outer policy: the offline group records again.
    let _ = crate::lra::check_with_lia_simplex(&arena, &assertions).expect("decided");
    let counters = last_lia_counters().expect("armed");
    assert!(
        counters.offline_calls > 0,
        "the outer OFFLINE_ONLY policy must be back in force: {counters:?}"
    );
    drop(outer);
}

#[test]
fn arming_the_counters_does_not_change_a_verdict() {
    // Diagnostic only. Nothing in the search reads these, and this is the
    // control that says so rather than the doc comment claiming it.
    let (arena, assertions) = searching_query();
    let plain = crate::lia_online::check_qf_lia_online(&arena, &assertions, &default_config())
        .expect("decidable");
    let armed = {
        let _guard = LiaCountersGuard::enable();
        crate::lia_online::check_qf_lia_online(&arena, &assertions, &default_config())
            .expect("decidable")
    };
    assert_eq!(
        std::mem::discriminant(&plain),
        std::mem::discriminant(&armed),
        "verdict changed under instrumentation: {plain:?} vs {armed:?}"
    );
}

fn default_config() -> SolverConfig {
    SolverConfig::default()
}
