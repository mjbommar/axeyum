//! **Which committed `Int` transition systems actually reach the interpolant?**
//!
//! `horn.rs::dispatch` tries `prove_safety_pdr_lia` FIRST and reaches
//! `prove_safety_imc_lia` — the only production consumer of an *integer*
//! Craig interpolant in this tree — only on `PdrLiaOutcome::Unknown`. So a shape
//! PDR decides can never exercise the interpolant, however weak that interpolant
//! is. This probe runs BOTH engines over every `Int`-sorted `TransitionSystem`
//! committed to the repository (the four in `tests/imc_lia.rs` and the five in
//! `tests/pdr_lia.rs`, seven distinct systems) and prints the decision matrix.
//!
//! It is the falsifiable instrument behind the roadmap item 3.7 measurement
//! `docs/research/03-measurements/interpolation-consumer-gap-2026-09-10.md`,
//! which recommends DO NOT BUILD on the number this prints: measured 2026-09-10,
//! `systems=7 reach_imc=1 imc_rescues=1` — PDR decides six of seven, the one that
//! reaches IMC (`EvenStepperOddTarget`) is proven `Safe` by TODAY's interpolant,
//! and so the interpolant is the binding constraint on **0 of 7**. A PDR change
//! that pushes more shapes down to IMC, or a new `Int` system that IMC cannot
//! close, moves `reach_imc` / `imc_rescues` and re-opens item 3.7.
//!
//! `#[ignore]`d on purpose: it gates nothing (the engines have their own suites)
//! and exists to be re-run by hand when someone re-asks item 3.7's question:
//!
//! ```sh
//! cargo test -p axeyum-solver --features full \
//!     --test pdr_imc_lia_reachability_probe -- --ignored --nocapture
//! ```
#![cfg(feature = "full")]

use axeyum_ir::{Sort, SymbolId, TermArena, TermId};
use axeyum_solver::{
    ImcLiaOutcome, PdrLiaOutcome, SolverConfig, SolverError, TransitionSystem,
    prove_safety_imc_lia, prove_safety_pdr_lia,
};

fn int_var(arena: &mut TermArena, step: usize) -> SymbolId {
    arena.declare(&format!("x@{step}"), Sort::Int).unwrap()
}

/// `init : x >= 0`, `trans : x' = x + 1`, `bad : x < 0` (`imc_lia.rs`).
struct MonotoneLowerBound;
impl TransitionSystem for MonotoneLowerBound {
    fn state_vars(&self, arena: &mut TermArena, step: usize) -> Result<Vec<SymbolId>, SolverError> {
        Ok(vec![int_var(arena, step)])
    }
    fn init(&self, arena: &mut TermArena, s0: &[SymbolId]) -> Result<TermId, SolverError> {
        let x = arena.var(s0[0]);
        let zero = arena.int_const(0);
        Ok(arena.int_ge(x, zero)?)
    }
    fn trans(
        &self,
        arena: &mut TermArena,
        pre: &[SymbolId],
        post: &[SymbolId],
    ) -> Result<TermId, SolverError> {
        let x = arena.var(pre[0]);
        let one = arena.int_const(1);
        let inc = arena.int_add(x, one)?;
        let x_next = arena.var(post[0]);
        Ok(arena.eq(x_next, inc)?)
    }
    fn bad(&self, arena: &mut TermArena, s: &[SymbolId]) -> Result<TermId, SolverError> {
        let x = arena.var(s[0]);
        let zero = arena.int_const(0);
        Ok(arena.int_lt(x, zero)?)
    }
}

/// `init : x = 0`, `trans : x' = x + 1`, `bad : x < 0`.
/// Byte-identical in `imc_lia.rs` and `pdr_lia.rs` (doc comment aside).
struct IntAccumulator;
impl TransitionSystem for IntAccumulator {
    fn state_vars(&self, arena: &mut TermArena, step: usize) -> Result<Vec<SymbolId>, SolverError> {
        Ok(vec![int_var(arena, step)])
    }
    fn init(&self, arena: &mut TermArena, s0: &[SymbolId]) -> Result<TermId, SolverError> {
        let x = arena.var(s0[0]);
        let zero = arena.int_const(0);
        Ok(arena.eq(x, zero)?)
    }
    fn trans(
        &self,
        arena: &mut TermArena,
        pre: &[SymbolId],
        post: &[SymbolId],
    ) -> Result<TermId, SolverError> {
        let x = arena.var(pre[0]);
        let one = arena.int_const(1);
        let inc = arena.int_add(x, one)?;
        let x_next = arena.var(post[0]);
        Ok(arena.eq(x_next, inc)?)
    }
    fn bad(&self, arena: &mut TermArena, s: &[SymbolId]) -> Result<TermId, SolverError> {
        let x = arena.var(s[0]);
        let zero = arena.int_const(0);
        Ok(arena.int_lt(x, zero)?)
    }
}

/// `init : x = 0 \/ x = 10`, `trans : x' = x`, `bad : 1 <= x <= 9` (`imc_lia.rs`).
struct DisjunctiveTwoRegion;
impl TransitionSystem for DisjunctiveTwoRegion {
    fn state_vars(&self, arena: &mut TermArena, step: usize) -> Result<Vec<SymbolId>, SolverError> {
        Ok(vec![int_var(arena, step)])
    }
    fn init(&self, arena: &mut TermArena, s0: &[SymbolId]) -> Result<TermId, SolverError> {
        let x = arena.var(s0[0]);
        let zero = arena.int_const(0);
        let ten = arena.int_const(10);
        let at_zero = arena.eq(x, zero)?;
        let at_ten = arena.eq(x, ten)?;
        Ok(arena.or(at_zero, at_ten)?)
    }
    fn trans(
        &self,
        arena: &mut TermArena,
        pre: &[SymbolId],
        post: &[SymbolId],
    ) -> Result<TermId, SolverError> {
        let x = arena.var(pre[0]);
        let x_next = arena.var(post[0]);
        Ok(arena.eq(x_next, x)?)
    }
    fn bad(&self, arena: &mut TermArena, s: &[SymbolId]) -> Result<TermId, SolverError> {
        let x = arena.var(s[0]);
        let one = arena.int_const(1);
        let nine = arena.int_const(9);
        let lower = arena.int_ge(x, one)?;
        let upper = arena.int_le(x, nine)?;
        Ok(arena.and(lower, upper)?)
    }
}

/// `init : x = 0 /\ y = 0`, `trans : x'=x+1 /\ y'=y+1`, `bad : x < y` (`pdr_lia.rs`).
struct TwinCounters;
impl TransitionSystem for TwinCounters {
    fn state_vars(&self, arena: &mut TermArena, step: usize) -> Result<Vec<SymbolId>, SolverError> {
        Ok(vec![
            arena.declare(&format!("x@{step}"), Sort::Int)?,
            arena.declare(&format!("y@{step}"), Sort::Int)?,
        ])
    }
    fn init(&self, arena: &mut TermArena, s0: &[SymbolId]) -> Result<TermId, SolverError> {
        let zero = arena.int_const(0);
        let x = arena.var(s0[0]);
        let y = arena.var(s0[1]);
        let xz = arena.eq(x, zero)?;
        let yz = arena.eq(y, zero)?;
        Ok(arena.and(xz, yz)?)
    }
    fn trans(
        &self,
        arena: &mut TermArena,
        pre: &[SymbolId],
        post: &[SymbolId],
    ) -> Result<TermId, SolverError> {
        let one = arena.int_const(1);
        let x = arena.var(pre[0]);
        let y = arena.var(pre[1]);
        let xn = arena.var(post[0]);
        let yn = arena.var(post[1]);
        let xinc = arena.int_add(x, one)?;
        let yinc = arena.int_add(y, one)?;
        let cx = arena.eq(xn, xinc)?;
        let cy = arena.eq(yn, yinc)?;
        Ok(arena.and(cx, cy)?)
    }
    fn bad(&self, arena: &mut TermArena, s: &[SymbolId]) -> Result<TermId, SolverError> {
        let x = arena.var(s[0]);
        let y = arena.var(s[1]);
        Ok(arena.int_lt(x, y)?)
    }
}

/// `init : x = 0`, `trans : x' = x + 2`, `bad : x = 1` (`pdr_lia.rs`).
struct EvenStepperOddTarget;
impl TransitionSystem for EvenStepperOddTarget {
    fn state_vars(&self, arena: &mut TermArena, step: usize) -> Result<Vec<SymbolId>, SolverError> {
        Ok(vec![int_var(arena, step)])
    }
    fn init(&self, arena: &mut TermArena, s0: &[SymbolId]) -> Result<TermId, SolverError> {
        let x = arena.var(s0[0]);
        let zero = arena.int_const(0);
        Ok(arena.eq(x, zero)?)
    }
    fn trans(
        &self,
        arena: &mut TermArena,
        pre: &[SymbolId],
        post: &[SymbolId],
    ) -> Result<TermId, SolverError> {
        let x = arena.var(pre[0]);
        let two = arena.int_const(2);
        let inc = arena.int_add(x, two)?;
        let x_next = arena.var(post[0]);
        Ok(arena.eq(x_next, inc)?)
    }
    fn bad(&self, arena: &mut TermArena, s: &[SymbolId]) -> Result<TermId, SolverError> {
        let x = arena.var(s[0]);
        let one = arena.int_const(1);
        Ok(arena.eq(x, one)?)
    }
}

/// `init : x = 0`, `trans : x' = x + 1`, `bad : x = 3` (both files). UNSAFE.
struct ReachesThree;
impl TransitionSystem for ReachesThree {
    fn state_vars(&self, arena: &mut TermArena, step: usize) -> Result<Vec<SymbolId>, SolverError> {
        Ok(vec![int_var(arena, step)])
    }
    fn init(&self, arena: &mut TermArena, s0: &[SymbolId]) -> Result<TermId, SolverError> {
        let x = arena.var(s0[0]);
        let zero = arena.int_const(0);
        Ok(arena.eq(x, zero)?)
    }
    fn trans(
        &self,
        arena: &mut TermArena,
        pre: &[SymbolId],
        post: &[SymbolId],
    ) -> Result<TermId, SolverError> {
        let x = arena.var(pre[0]);
        let one = arena.int_const(1);
        let inc = arena.int_add(x, one)?;
        let x_next = arena.var(post[0]);
        Ok(arena.eq(x_next, inc)?)
    }
    fn bad(&self, arena: &mut TermArena, s: &[SymbolId]) -> Result<TermId, SolverError> {
        let x = arena.var(s[0]);
        let three = arena.int_const(3);
        Ok(arena.eq(x, three)?)
    }
}

/// `init : x = 0`, `trans : x' = x + 1`, `bad : x >= 5` (`pdr_lia.rs`). UNSAFE.
struct UnboundedReachesFive;
impl TransitionSystem for UnboundedReachesFive {
    fn state_vars(&self, arena: &mut TermArena, step: usize) -> Result<Vec<SymbolId>, SolverError> {
        Ok(vec![int_var(arena, step)])
    }
    fn init(&self, arena: &mut TermArena, s0: &[SymbolId]) -> Result<TermId, SolverError> {
        let x = arena.var(s0[0]);
        let zero = arena.int_const(0);
        Ok(arena.eq(x, zero)?)
    }
    fn trans(
        &self,
        arena: &mut TermArena,
        pre: &[SymbolId],
        post: &[SymbolId],
    ) -> Result<TermId, SolverError> {
        let x = arena.var(pre[0]);
        let one = arena.int_const(1);
        let inc = arena.int_add(x, one)?;
        let x_next = arena.var(post[0]);
        Ok(arena.eq(x_next, inc)?)
    }
    fn bad(&self, arena: &mut TermArena, s: &[SymbolId]) -> Result<TermId, SolverError> {
        let x = arena.var(s[0]);
        let five = arena.int_const(5);
        Ok(arena.int_ge(x, five)?)
    }
}

fn pdr_verdict<S: TransitionSystem>(sys: &S) -> &'static str {
    let mut arena = TermArena::new();
    match prove_safety_pdr_lia(&mut arena, sys, &SolverConfig::default()) {
        Ok(PdrLiaOutcome::Safe { .. }) => "SAFE",
        Ok(PdrLiaOutcome::Reachable { .. }) => "REACHABLE",
        Ok(PdrLiaOutcome::Unknown { .. }) => "unknown",
        Err(_) => "ERR",
    }
}

fn imc_verdict<S: TransitionSystem>(sys: &S) -> &'static str {
    let mut arena = TermArena::new();
    match prove_safety_imc_lia(&mut arena, sys, &SolverConfig::default()) {
        Ok(ImcLiaOutcome::Safe { .. }) => "SAFE",
        Ok(ImcLiaOutcome::Reachable { .. }) => "REACHABLE",
        Ok(ImcLiaOutcome::Unknown { .. }) => "unknown",
        Err(_) => "ERR",
    }
}

macro_rules! row {
    ($name:expr, $sys:expr) => {{
        let p = pdr_verdict(&$sys);
        let i = imc_verdict(&$sys);
        let reaches_imc = if p == "unknown" { "YES" } else { "no" };
        println!(
            "{:<24} pdr={:<10} imc={:<10} imc_reached_in_horn={reaches_imc}",
            $name, p, i
        );
        (p, i, p == "unknown")
    }};
}

#[test]
#[ignore = "a hand-run measurement instrument for roadmap item 3.7, not a gate"]
fn pdr_imc_decision_matrix() {
    println!("--- M3-7 PDR x IMC matrix over every committed Int transition system ---");
    let rows = [
        row!("MonotoneLowerBound", MonotoneLowerBound),
        row!("IntAccumulator", IntAccumulator),
        row!("DisjunctiveTwoRegion", DisjunctiveTwoRegion),
        row!("TwinCounters", TwinCounters),
        row!("EvenStepperOddTarget", EvenStepperOddTarget),
        row!("ReachesThree", ReachesThree),
        row!("UnboundedReachesFive", UnboundedReachesFive),
    ];
    let total = rows.len();
    let reach_imc = rows.iter().filter(|r| r.2).count();
    let imc_rescues = rows
        .iter()
        .filter(|r| r.2 && (r.1 == "SAFE" || r.1 == "REACHABLE"))
        .count();
    println!("--- systems={total} reach_imc={reach_imc} imc_rescues={imc_rescues} ---");
    assert_eq!(total, 7, "coverage: all seven committed Int systems ran");
}
