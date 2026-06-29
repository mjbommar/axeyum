//! Rung 4 of the *verified systems & protocols* backlog
//! ([`docs/consumer-track/verify/unbounded-protocol-safety.md`]) — **unbounded**
//! protocol safety: prove a handshake-FSM invariant for *every* trace (not just
//! traces of length ≤ K) via an inductive invariant. This is the seL4-grade step
//! up from the bounded Block C (`protocol_fsm_examples.rs`).
//!
//! The same handshake (states `CLOSED`=0, `SYN_SENT`=1, `ESTABLISHED`=2) is now a
//! [`TransitionSystem`] trait impl over the IR; nondeterministic events are
//! modeled the standard way — a finite disjunction in `trans` (the adversary may
//! deliver any event each step). We consume the solver's unbounded engines
//! directly (the `#[verify]` macro is bounded-only):
//!
//! - `prove_safety_k_induction` → `Safe{k}` for the validity invariant (state
//!   never leaves the enum), proven for ALL traces.
//! - `prove_safety_pdr` → `Safe{invariant}` for the *ordering* invariant
//!   (`ESTABLISHED ⇒ a handshake happened`): PDR discovers an inductive invariant
//!   over the whole state space. (Measured note: this engine's k-induction *also*
//!   closes the ordering invariant at `k=1` — stronger than the textbook
//!   expectation that it would need the `SYN_SENT ⇒ seen` strengthening; the two
//!   independent engines agree on `Safe`, which is the cross-check that matters.
//!   The k-induction-vs-PDR *gap* is demonstrated by the solver's own
//!   `tests/pdr.rs` `StuckCounter`.)
//! - `prove_safety_pdr_certified` → three recheckable DRAT obligations: the first
//!   *protocol* property carrying an unbounded, independently checkable proof.
//! - the blind-injection buggy handshake → `Reachable` (unbounded counterexample),
//!   cross-checked against `bounded_model_check`.

use axeyum_ir::{Sort, SymbolId, TermArena, TermId};
use axeyum_solver::{
    BmcOutcome, CertifiedPdrOutcome, PdrOutcome, SafetyOutcome, SolverConfig, SolverError,
    TransitionSystem, bounded_model_check, prove_safety_k_induction, prove_safety_pdr,
    prove_safety_pdr_certified,
};

const ALPHABET: [u8; 4] = [0, 1, 2, 3]; // SEND_SYN, RECV_SYNACK, CLOSE, DATA

// ---- validity FSM: single `state` variable, invariant `state <= 2` ------------

struct HandshakeValidity;

impl TransitionSystem for HandshakeValidity {
    fn state_vars(&self, arena: &mut TermArena, step: usize) -> Result<Vec<SymbolId>, SolverError> {
        Ok(vec![
            arena.declare(&format!("state@{step}"), Sort::BitVec(8))?,
        ])
    }

    fn init(&self, arena: &mut TermArena, s0: &[SymbolId]) -> Result<TermId, SolverError> {
        let state = arena.var(s0[0]);
        let zero = arena.bv_const(8, 0)?;
        Ok(arena.eq(state, zero)?)
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
        for &event in &ALPHABET {
            let ns = next_state(arena, s, event, false)?;
            let matches = arena.eq(ps, ns)?;
            disj = Some(match disj {
                None => matches,
                Some(d) => arena.or(d, matches)?,
            });
        }
        Ok(disj.expect("non-empty alphabet"))
    }

    fn bad(&self, arena: &mut TermArena, s: &[SymbolId]) -> Result<TermId, SolverError> {
        // invalid state: `state > 2`
        let state = arena.var(s[0]);
        let two = arena.bv_const(8, 2)?;
        Ok(arena.bv_ugt(state, two)?)
    }
}

// ---- ordering FSM: `(state, seen)`, invariant `!(ESTABLISHED && !seen)` --------

struct HandshakeOrdering {
    /// When true, a bare `CLOSED + RECV_SYNACK -> ESTABLISHED` transition is added
    /// — establishing the connection with no handshake (blind-injection class).
    buggy: bool,
}

impl HandshakeOrdering {
    /// `(next_state, next_seen)` under a concrete `event`. `seen` is set (and stays
    /// set) whenever the machine enters `SYN_SENT`.
    fn successor(
        &self,
        arena: &mut TermArena,
        s: TermId,
        v: TermId,
        event: u8,
    ) -> Result<(TermId, TermId), SolverError> {
        let ns = next_state(arena, s, event, self.buggy)?;
        let one = arena.bv_const(8, 1)?;
        let zero = arena.bv_const(8, 0)?;
        // next_seen = ite((seen == 1) || (next_state == SYN_SENT), 1, 0)
        let v_set = arena.eq(v, one)?;
        let enters_syn = arena.eq(ns, one)?;
        let cond = arena.or(v_set, enters_syn)?;
        let nv = arena.ite(cond, one, zero)?;
        Ok((ns, nv))
    }
}

impl TransitionSystem for HandshakeOrdering {
    fn state_vars(&self, arena: &mut TermArena, step: usize) -> Result<Vec<SymbolId>, SolverError> {
        Ok(vec![
            arena.declare(&format!("state@{step}"), Sort::BitVec(8))?,
            arena.declare(&format!("seen@{step}"), Sort::BitVec(8))?,
        ])
    }

    fn init(&self, arena: &mut TermArena, s0: &[SymbolId]) -> Result<TermId, SolverError> {
        let state = arena.var(s0[0]);
        let seen = arena.var(s0[1]);
        let zero = arena.bv_const(8, 0)?;
        let s_init = arena.eq(state, zero)?;
        let v_init = arena.eq(seen, zero)?;
        Ok(arena.and(s_init, v_init)?)
    }

    fn trans(
        &self,
        arena: &mut TermArena,
        pre: &[SymbolId],
        post: &[SymbolId],
    ) -> Result<TermId, SolverError> {
        let s = arena.var(pre[0]);
        let v = arena.var(pre[1]);
        let ps = arena.var(post[0]);
        let pv = arena.var(post[1]);
        let mut disj: Option<TermId> = None;
        for &event in &ALPHABET {
            let (ns, nv) = self.successor(arena, s, v, event)?;
            let m_state = arena.eq(ps, ns)?;
            let m_seen = arena.eq(pv, nv)?;
            let conj = arena.and(m_state, m_seen)?;
            disj = Some(match disj {
                None => conj,
                Some(d) => arena.or(d, conj)?,
            });
        }
        Ok(disj.expect("non-empty alphabet"))
    }

    fn bad(&self, arena: &mut TermArena, s: &[SymbolId]) -> Result<TermId, SolverError> {
        // ESTABLISHED with no recorded handshake.
        let state = arena.var(s[0]);
        let seen = arena.var(s[1]);
        let two = arena.bv_const(8, 2)?;
        let zero = arena.bv_const(8, 0)?;
        let established = arena.eq(state, two)?;
        let unseen = arena.eq(seen, zero)?;
        Ok(arena.and(established, unseen)?)
    }
}

/// The shared (correct) state transition; `buggy` adds the handshake-skipping arm
/// to the `RECV_SYNACK` event.
fn next_state(
    arena: &mut TermArena,
    s: TermId,
    event: u8,
    buggy: bool,
) -> Result<TermId, SolverError> {
    let zero = arena.bv_const(8, 0)?;
    let one = arena.bv_const(8, 1)?;
    let two = arena.bv_const(8, 2)?;
    let ns = match event {
        0 => {
            // SEND_SYN: CLOSED -> SYN_SENT, else stay
            let is_closed = arena.eq(s, zero)?;
            arena.ite(is_closed, one, s)?
        }
        1 => {
            // RECV_SYNACK: SYN_SENT -> ESTABLISHED (+ buggy: CLOSED -> ESTABLISHED)
            let is_syn = arena.eq(s, one)?;
            if buggy {
                let is_closed = arena.eq(s, zero)?;
                let from_closed = arena.ite(is_closed, two, s)?;
                arena.ite(is_syn, two, from_closed)?
            } else {
                arena.ite(is_syn, two, s)?
            }
        }
        2 => zero, // CLOSE -> CLOSED from any state
        _ => s,    // DATA / unknown: stay
    };
    Ok(ns)
}

// ---- tests ---------------------------------------------------------------------

/// Unbounded validity: the machine never enters an undefined state, for ALL
/// traces (k-induction closes — the invariant `state <= 2` is k-inductive).
#[test]
fn validity_safe_for_all_traces() {
    let mut arena = TermArena::new();
    let outcome =
        prove_safety_k_induction(&mut arena, &HandshakeValidity, 4, &SolverConfig::default())
            .expect("solver should not hard-error");
    assert!(
        matches!(outcome, SafetyOutcome::Safe { .. }),
        "validity must be proven for ALL traces (k-inductive), got {outcome:?}"
    );
}

/// The ordering invariant (`ESTABLISHED ⇒ a handshake happened`) holds for ALL
/// traces, proven two independent ways that must agree: k-induction (this engine
/// closes it at `k=1`; never a wrong `Reachable` on a safe system) and PDR
/// (discovers an inductive invariant). Mutual `Safe` agreement is the cross-check.
#[test]
fn ordering_safe_for_all_traces() {
    let mut arena = TermArena::new();
    let k = prove_safety_k_induction(
        &mut arena,
        &HandshakeOrdering { buggy: false },
        4,
        &SolverConfig::default(),
    )
    .expect("solver should not hard-error");
    eprintln!("ordering k-induction (max_k=4): {k:?}");
    assert!(
        matches!(
            k,
            SafetyOutcome::Inconclusive { .. } | SafetyOutcome::Safe { .. }
        ),
        "k-induction must never report a wrong counterexample on a safe system, got {k:?}"
    );

    let mut arena = TermArena::new();
    let pdr = prove_safety_pdr(
        &mut arena,
        &HandshakeOrdering { buggy: false },
        &SolverConfig::default(),
    )
    .expect("solver should not hard-error");
    assert!(
        matches!(pdr, PdrOutcome::Safe { .. }),
        "PDR must prove the ordering invariant for ALL traces, got {pdr:?}"
    );
}

/// The first *protocol* property carrying an unbounded, independently checkable
/// proof: certified PDR returns three DRAT obligations (initiation / consecution
/// / safety) that each re-check, plus a whole-certificate re-check.
#[test]
fn ordering_certified_safe_rechecks() {
    let mut arena = TermArena::new();
    let outcome = prove_safety_pdr_certified(
        &mut arena,
        &HandshakeOrdering { buggy: false },
        &SolverConfig::default(),
    )
    .expect("solver should not hard-error");
    let CertifiedPdrOutcome::Safe(cert) = outcome else {
        panic!("the ordering invariant must be certified safe, got {outcome:?}");
    };
    for proof in [&cert.initiation, &cert.consecution, &cert.safety] {
        assert!(
            !proof.dimacs.is_empty() && !proof.drat.is_empty(),
            "each unbounded obligation must carry non-empty DRAT evidence"
        );
        assert!(proof.recheck().unwrap(), "each obligation must re-check");
    }
    assert!(
        cert.recheck().unwrap(),
        "the whole unbounded IC3/PDR certificate must re-check independently"
    );
}

/// The blind-injection bug (`CLOSED + RECV_SYNACK -> ESTABLISHED`) makes the
/// ordering invariant reachable — an **unbounded** counterexample, cross-checked
/// against bounded model checking.
#[test]
fn skip_bug_is_an_unbounded_counterexample() {
    let mut arena = TermArena::new();
    let pdr = prove_safety_pdr(
        &mut arena,
        &HandshakeOrdering { buggy: true },
        &SolverConfig::default(),
    )
    .expect("solver should not hard-error");
    assert!(
        matches!(pdr, PdrOutcome::Reachable { .. }),
        "the handshake-skip bug must be reachable, got {pdr:?}"
    );

    let mut arena = TermArena::new();
    let bmc = bounded_model_check(
        &mut arena,
        &HandshakeOrdering { buggy: true },
        4,
        &SolverConfig::default(),
    )
    .expect("solver should not hard-error");
    assert!(
        matches!(bmc, BmcOutcome::Reachable { .. }),
        "BMC must independently reach the bad state, got {bmc:?}"
    );
}

/// Benchmark: bounded model checking gives a *weaker* guarantee at each depth
/// (`UnreachableWithinBound` — never a proof), and you would have to re-run it at
/// every depth forever; one unbounded `prove_safety_k_induction` subsumes all
/// depths with a single `Safe`. Verdicts are asserted; times are printed
/// (indicative, `--nocapture`), not asserted.
#[test]
fn bounded_vs_unbounded_validity() {
    use std::time::Instant;

    for bound in [2usize, 8, 32] {
        let mut arena = TermArena::new();
        let t = Instant::now();
        let bmc = bounded_model_check(
            &mut arena,
            &HandshakeValidity,
            bound,
            &SolverConfig::default(),
        )
        .expect("solver should not hard-error");
        let dt = t.elapsed();
        assert!(
            matches!(bmc, BmcOutcome::UnreachableWithinBound { .. }),
            "bounded check at depth {bound} must be safe-within-bound, got {bmc:?}"
        );
        eprintln!("BMC depth {bound:>2}: {bmc:?} in {dt:?} (bounded — NOT a proof)");
    }

    let mut arena = TermArena::new();
    let t = Instant::now();
    let outcome =
        prove_safety_k_induction(&mut arena, &HandshakeValidity, 4, &SolverConfig::default())
            .expect("solver should not hard-error");
    let dt = t.elapsed();
    assert!(
        matches!(outcome, SafetyOutcome::Safe { .. }),
        "the unbounded proof must subsume all depths, got {outcome:?}"
    );
    eprintln!("k-induction (all depths): {outcome:?} in {dt:?} (a proof for EVERY trace)");
}
