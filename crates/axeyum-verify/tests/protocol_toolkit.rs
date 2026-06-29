//! An ergonomic protocol toolkit (design:
//! [`docs/consumer-track/verify/protocol-toolkit.md`]) — the *"natural, easy to
//! use"* half of the goal. A declarative [`Fsm`] (states, init, events, a
//! transition closure, and a bad-state set) compiles to a generic
//! [`TransitionSystem`] and is proven **bounded** (`find_bug`) and **unbounded**
//! (`prove_for_all_traces`) in a handful of lines — the informal state diagram
//! *is* the code. This is the reusable consumer-side workflow the hand-written
//! `protocol_unbounded.rs` motivates; no solver-internals changes.
//!
//! Temporal properties are expressed by **state-splitting**: fold the safety
//! automaton into the state (e.g. a distinct `BAD_ESTABLISHED` state the correct
//! machine never enters), so reachability-safety over the product state covers
//! the temporal properties protocols care about — no ghost plumbing in the toolkit.

#![allow(clippy::similar_names)]

use axeyum_ir::{Sort, SymbolId, TermArena, TermId};
use axeyum_solver::{
    BmcOutcome, PdrOutcome, SolverConfig, SolverError, TransitionSystem, bounded_model_check,
    prove_safety_pdr,
};

/// A finite-state protocol machine. Valid states are `0..states`; the event
/// alphabet is `0..events`, delivered nondeterministically each step. `step` is
/// the transition *table* as a closure `(state, event) -> next_state`; `bad` is
/// the set of unsafe states (the safety property is "no `bad` state is reachable").
struct Fsm<F> {
    states: u8,
    init: u8,
    events: u8,
    step: F,
    bad: Vec<u8>,
}

impl<F: Fn(u8, u8) -> u8> Fsm<F> {
    /// `next_e(state)` as a nested `ite` over the concrete from-states, built
    /// automatically from the `step` table (default: stay).
    fn next_under_event(
        &self,
        arena: &mut TermArena,
        state: TermId,
        event: u8,
    ) -> Result<TermId, SolverError> {
        let mut acc = state; // default: stay (covers any out-of-range value)
        for from in (0..self.states).rev() {
            let from_c = arena.bv_const(8, u128::from(from))?;
            let to_c = arena.bv_const(8, u128::from((self.step)(from, event)))?;
            let is_from = arena.eq(state, from_c)?;
            acc = arena.ite(is_from, to_c, acc)?;
        }
        Ok(acc)
    }

    /// Prove the safety property for **every** trace (PDR discovers an inductive
    /// invariant): `Safe{invariant}` / `Reachable{..}` / `Unknown{..}`.
    fn prove_for_all_traces(&self) -> PdrOutcome {
        let mut arena = TermArena::new();
        prove_safety_pdr(&mut arena, self, &SolverConfig::default())
            .expect("solver should not hard-error")
    }

    /// Bounded counterexample search up to `depth` (the rung-3 contrast).
    fn find_bug(&self, depth: usize) -> BmcOutcome {
        let mut arena = TermArena::new();
        bounded_model_check(&mut arena, self, depth, &SolverConfig::default())
            .expect("solver should not hard-error")
    }
}

impl<F: Fn(u8, u8) -> u8> TransitionSystem for Fsm<F> {
    fn state_vars(&self, arena: &mut TermArena, step: usize) -> Result<Vec<SymbolId>, SolverError> {
        Ok(vec![
            arena.declare(&format!("state@{step}"), Sort::BitVec(8))?,
        ])
    }

    fn init(&self, arena: &mut TermArena, s0: &[SymbolId]) -> Result<TermId, SolverError> {
        let state = arena.var(s0[0]);
        let init = arena.bv_const(8, u128::from(self.init))?;
        Ok(arena.eq(state, init)?)
    }

    fn trans(
        &self,
        arena: &mut TermArena,
        pre: &[SymbolId],
        post: &[SymbolId],
    ) -> Result<TermId, SolverError> {
        let s = arena.var(pre[0]);
        let ps = arena.var(post[0]);
        let mut disj: Option<TermId> = None;
        for event in 0..self.events {
            let next = self.next_under_event(arena, s, event)?;
            let matches = arena.eq(ps, next)?;
            disj = Some(match disj {
                None => matches,
                Some(d) => arena.or(d, matches)?,
            });
        }
        Ok(disj.expect("event alphabet must be non-empty"))
    }

    fn bad(&self, arena: &mut TermArena, s: &[SymbolId]) -> Result<TermId, SolverError> {
        let state = arena.var(s[0]);
        let mut disj: Option<TermId> = None;
        for &b in &self.bad {
            let b_c = arena.bv_const(8, u128::from(b))?;
            let is_bad = arena.eq(state, b_c)?;
            disj = Some(match disj {
                None => is_bad,
                Some(d) => arena.or(d, is_bad)?,
            });
        }
        if let Some(d) = disj {
            Ok(d)
        } else {
            // No bad states: `bad` is unsatisfiable (`0 == 1`).
            let zero = arena.bv_const(8, 0)?;
            let one = arena.bv_const(8, 1)?;
            Ok(arena.eq(zero, one)?)
        }
    }
}

// ---- declarative handshake (ordering via state-splitting) ----------------------

// states
const CLOSED: u8 = 0;
const SYN_SENT: u8 = 1;
const ESTABLISHED: u8 = 2;
const BAD_ESTABLISHED: u8 = 3; // established with no handshake (the safety automaton)
// events
const SEND_SYN: u8 = 0;
const RECV_SYNACK: u8 = 1;
const CLOSE: u8 = 2;

/// The handshake transition table. `buggy` adds the blind-injection arm
/// `CLOSED + RECV_SYNACK -> BAD_ESTABLISHED` (establishing with no SYN).
fn handshake_step(buggy: bool) -> impl Fn(u8, u8) -> u8 {
    move |state, event| match (state, event) {
        (CLOSED, SEND_SYN) => SYN_SENT,
        (SYN_SENT, RECV_SYNACK) => ESTABLISHED,
        (CLOSED, RECV_SYNACK) if buggy => BAD_ESTABLISHED,
        (_, CLOSE) => CLOSED,
        (s, _) => s, // otherwise stay
    }
}

fn handshake(buggy: bool) -> Fsm<impl Fn(u8, u8) -> u8> {
    Fsm {
        states: 4,
        init: CLOSED,
        events: 4, // SEND_SYN, RECV_SYNACK, CLOSE, DATA
        step: handshake_step(buggy),
        bad: vec![BAD_ESTABLISHED],
    }
}

/// The correct handshake never establishes without a handshake — proven for ALL
/// traces in ~10 lines of declarative spec (vs. the ~50-line hand-written
/// `TransitionSystem` in `protocol_unbounded.rs`, which reaches the same verdict).
#[test]
fn declarative_handshake_safe_for_all_traces() {
    let outcome = handshake(false).prove_for_all_traces();
    assert!(
        matches!(outcome, PdrOutcome::Safe { .. }),
        "the correct handshake must be safe for all traces, got {outcome:?}"
    );
}

/// The blind-injection bug is caught — unbounded `Reachable` (PDR) and a bounded
/// counterexample (BMC) agree, the cross-check.
#[test]
fn declarative_handshake_skip_bug_is_reachable() {
    let outcome = handshake(true).prove_for_all_traces();
    assert!(
        matches!(outcome, PdrOutcome::Reachable { .. }),
        "the handshake-skip bug must be reachable, got {outcome:?}"
    );
    let bmc = handshake(true).find_bug(4);
    assert!(
        matches!(bmc, BmcOutcome::Reachable { .. }),
        "BMC must independently reach the bad state, got {bmc:?}"
    );
}

/// The correct machine has no bounded counterexample either (`UnreachableWithinBound`),
/// consistent with the unbounded `Safe` — toolkit verdicts cohere across engines.
#[test]
fn declarative_handshake_safe_has_no_bounded_bug() {
    let bmc = handshake(false).find_bug(8);
    assert!(
        matches!(bmc, BmcOutcome::UnreachableWithinBound { .. }),
        "the correct handshake must have no bug within bound, got {bmc:?}"
    );
}
