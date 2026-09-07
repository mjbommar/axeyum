//! Micro-benchmark for the difference-logic route (`crate::dl_online`,
//! `QF_IDL`) through the full `check_auto` dispatch ladder — see
//! `docs/research/12-performance/bench-theories-2026-09-07.md`.
//!
//! There was no bench of any kind on this route before this file, and per the
//! same doc's diary it moved onto the native `CdclT` core recently, so this is
//! also the first timing baseline post-move.
//!
//! What this proxies: a job-shop / scheduling-style precedence chain is the
//! textbook `QF_IDL` shape (`task_{i+1} - task_i >= duration_i`, i.e.
//! `task_i - task_{i+1} <= -duration_i`) — every corpus family that names
//! difference logic in this repo's docs is a scheduling or timed-automaton
//! encoding, never a random graph. Two fixtures over the same chain isolate
//! the two costs [`dl_online`] names in its module doc: incremental
//! Cotton–Maler feasibility propagation (`CHAIN`, satisfiable, no cycle ever
//! closes) versus Farkas-checked negative-cycle detection and refutation
//! (`CHAIN_CYCLE`, one constraint added at the end that closes a cycle through
//! the whole chain, forcing `unsat`).
//!
//! Requires the `full` feature (the `auto` dispatch module, and with it
//! `check_auto`, is `#[cfg(feature = "full")]`).

#![allow(missing_docs)] // criterion_group!/criterion_main! expand to undocumented items; see module doc.

use std::hint::black_box;

use axeyum_ir::{Sort, TermArena, TermId};
use axeyum_solver::{CheckResult, SolverConfig, check_auto};
use criterion::{Criterion, criterion_group, criterion_main};

/// Chain length: `CHAIN_LEN + 1` tasks, `CHAIN_LEN` precedence edges. Large
/// enough that a per-assert `O(|V|)` allocation (the trap `dl_online`'s
/// `Scratch` doc calls out) would be visible, small enough that the whole
/// bench stays well under budget.
const CHAIN_LEN: usize = 400;

/// Builds `task_0 .. task_{CHAIN_LEN}` (`Int`) and the precedence chain
/// `task_i - task_{i+1} <= -1` for `i in 0..CHAIN_LEN` — every task must start
/// at least one tick after its predecessor. Satisfiable by construction
/// (`task_i = i`).
fn build_chain(arena: &mut TermArena) -> Vec<TermId> {
    let tasks: Vec<TermId> = (0..=CHAIN_LEN)
        .map(|i| {
            let sym = arena
                .declare(&format!("task_{i}"), Sort::Int)
                .expect("distinct declared name per task");
            arena.var(sym)
        })
        .collect();
    let neg_one = arena.int_const(-1);
    let mut assertions = Vec::with_capacity(CHAIN_LEN);
    for i in 0..CHAIN_LEN {
        let diff = arena
            .int_sub(tasks[i], tasks[i + 1])
            .expect("int_sub of two declared int vars");
        let edge = arena
            .int_le(diff, neg_one)
            .expect("int_le of a well-sorted int term and an int constant");
        assertions.push(edge);
    }
    assertions
}

/// The satisfiable chain (propagation-heavy, negative-cycle detection never
/// fires — every `assert` accepts).
fn bench_dl_chain_sat(c: &mut Criterion) {
    c.bench_function("dl_online_chain_sat", |b| {
        b.iter(|| {
            let mut arena = TermArena::new();
            let assertions = build_chain(&mut arena);
            let result = check_auto(&mut arena, &assertions, &SolverConfig::default())
                .expect("no solver error");
            assert!(
                matches!(result, CheckResult::Sat(_)),
                "the chain task_i - task_{{i+1}} <= -1 is satisfied by task_i = i"
            );
            black_box(result);
        });
    });
}

/// The same chain plus one closing edge `task_{CHAIN_LEN} - task_0 <= -1`,
/// which sums around the whole cycle to `<= -(CHAIN_LEN + 1)` while every
/// vertex's potential difference around a cycle must be `0` — infeasible by
/// construction, and the cycle spans the *entire* chain, so detection must
/// walk all of it (worst case for the Dijkstra-style `γ` propagation, not the
/// best case of a short local cycle).
fn bench_dl_chain_cycle_unsat(c: &mut Criterion) {
    c.bench_function("dl_online_chain_cycle_unsat", |b| {
        b.iter(|| {
            let mut arena = TermArena::new();
            let mut assertions = build_chain(&mut arena);
            let tasks: Vec<TermId> = (0..=CHAIN_LEN)
                .map(|i| {
                    let sym = arena
                        .find_symbol(&format!("task_{i}"))
                        .expect("declared by build_chain");
                    arena.var(sym)
                })
                .collect();
            let neg_one = arena.int_const(-1);
            let closing_diff = arena
                .int_sub(tasks[CHAIN_LEN], tasks[0])
                .expect("int_sub of two declared int vars");
            let closing_edge = arena
                .int_le(closing_diff, neg_one)
                .expect("int_le of a well-sorted int term and an int constant");
            assertions.push(closing_edge);
            let result = check_auto(&mut arena, &assertions, &SolverConfig::default())
                .expect("no solver error");
            assert!(
                matches!(result, CheckResult::Unsat),
                "the closing edge forces a cycle whose weights sum negative"
            );
            black_box(result);
        });
    });
}

criterion_group!(benches, bench_dl_chain_sat, bench_dl_chain_cycle_unsat);
criterion_main!(benches);
