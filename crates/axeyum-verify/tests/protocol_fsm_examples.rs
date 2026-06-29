//! Block C of the *verified systems & protocols* backlog
//! ([`docs/consumer-track/verify/protocol-state-machines.md`]) — bounded
//! protocol **state-machine** verification driving the real `#[axeyum::verify]`
//! macro. The step from "this function is safe" to "this *protocol* is safe for
//! any sequence of K events" (rung 3 → the rung-4 bridge).
//!
//! Encoding (no new macro features): state is a small `u8`, the adversary's event
//! trace is a fixed `[u8; K]`, and an `#[unwind(K)]`-bounded loop steps an inline
//! `if`-chain transition (a helper `fn` would be out of fragment — the macro
//! lowers one body) and `assert!`s the safety invariant after each step. A safe
//! machine VERIFIES (no K-length trace breaks the invariant — bounded model
//! checking); a buggy transition table yields a concrete bad **event trace**, and
//! the generated `expect_bug` test re-runs the original on that witness to
//! confirm it panics (DISAGREE = 0). Guarantees are **bounded** (trace length K).
//!
//! A tiny client handshake: states `CLOSED`=0, `SYN_SENT`=1, `ESTABLISHED`=2;
//! events (masked to the alphabet) `SEND_SYN`=0, `RECV_SYNACK`=1, `CLOSE`=2,
//! `DATA`=3.

#![allow(clippy::similar_names)]

use axeyum_verify::{Verdict, cert_coverage, verify};

// ---- Invariant class 1: validity (state never escapes the enum range) ----------

/// The correct transition table only ever yields a valid state `<= 2`, for every
/// event sequence of length 4 — a bounded model-checking proof that the machine
/// can never enter an undefined state.
#[verify]
#[axeyum_verify::unwind(4)]
fn handshake_validity_safe(events: [u8; 4]) -> u8 {
    let mut state: u8 = 0; // CLOSED
    let mut i: usize = 0;
    while i < 4 {
        let ev: u8 = events[i] & 0x3;
        let mut next: u8 = state; // default: stay
        if ev == 2 {
            next = 0; // CLOSE from any state -> CLOSED
        } else if state == 0 && ev == 0 {
            next = 1; // CLOSED + SEND_SYN -> SYN_SENT
        } else if state == 1 && ev == 1 {
            next = 2; // SYN_SENT + RECV_SYNACK -> ESTABLISHED
        }
        state = next;
        assert!(state <= 2); // validity invariant
        i += 1;
    }
    state
}

#[test]
fn handshake_validity_verifies() {
    match handshake_validity_safe__axeyum_verdict() {
        Verdict::Verified { .. } => {}
        other => panic!("the correct handshake must keep state valid, got {other:?}"),
    }
}

/// BUG: an off-by-one transition (`next = state + 1` instead of a table value)
/// when `RECV_SYNACK` arrives while already `ESTABLISHED` — the machine walks to
/// the undefined state 3. The trace `[SEND_SYN, RECV_SYNACK, RECV_SYNACK, _]`
/// reaches it; the validity invariant is then violable.
#[verify(expect_bug)]
#[axeyum_verify::unwind(4)]
fn handshake_validity_offbyone_bug(events: [u8; 4]) -> u8 {
    let mut state: u8 = 0;
    let mut i: usize = 0;
    while i < 4 {
        let ev: u8 = events[i] & 0x3;
        let mut next: u8 = state;
        if ev == 2 {
            next = 0;
        } else if state == 0 && ev == 0 {
            next = 1;
        } else if state == 1 && ev == 1 {
            next = 2;
        } else if state == 2 && ev == 1 {
            next = state + 1; // BUG: should stay (or be a table value); escapes to 3
        }
        state = next;
        assert!(state <= 2);
        i += 1;
    }
    state
}

// ---- Invariant class 2: protocol ordering (no ESTABLISHED without a handshake) --

/// A genuine temporal safety property folded into an auxiliary state bit: the
/// connection only reaches `ESTABLISHED` after passing through `SYN_SENT`.
/// `seen_syn_sent` is set whenever the machine enters `SYN_SENT`; the invariant
/// asserts it holds whenever the machine is `ESTABLISHED`. Verified for all traces.
#[verify]
#[axeyum_verify::unwind(4)]
fn handshake_ordering_safe(events: [u8; 4]) -> u8 {
    let mut state: u8 = 0;
    let mut seen_syn_sent: u8 = 0;
    let mut i: usize = 0;
    while i < 4 {
        let ev: u8 = events[i] & 0x3;
        let mut next: u8 = state;
        if ev == 2 {
            next = 0;
        } else if state == 0 && ev == 0 {
            next = 1;
        } else if state == 1 && ev == 1 {
            next = 2;
        }
        if next == 1 {
            seen_syn_sent = 1;
        }
        state = next;
        if state == 2 {
            assert!(seen_syn_sent == 1); // ESTABLISHED implies the handshake happened
        }
        i += 1;
    }
    state
}

#[test]
fn handshake_ordering_verifies() {
    match handshake_ordering_safe__axeyum_verdict() {
        Verdict::Verified { .. } => {}
        other => panic!("ESTABLISHED must require passing SYN_SENT, got {other:?}"),
    }
}

/// BUG: a transition that establishes the connection straight from `CLOSED` on a
/// bare `RECV_SYNACK` — no handshake (a blind-injection / spoofing class). The
/// single-event trace `[RECV_SYNACK, ..]` reaches ESTABLISHED with
/// `seen_syn_sent == 0`, violating the ordering invariant.
#[verify(expect_bug)]
#[axeyum_verify::unwind(4)]
fn handshake_skip_bug(events: [u8; 4]) -> u8 {
    let mut state: u8 = 0;
    let mut seen_syn_sent: u8 = 0;
    let mut i: usize = 0;
    while i < 4 {
        let ev: u8 = events[i] & 0x3;
        let mut next: u8 = state;
        if ev == 2 {
            next = 0;
        } else if state == 0 && ev == 0 {
            next = 1;
        } else if state == 1 && ev == 1 {
            next = 2;
        } else if state == 0 && ev == 1 {
            next = 2; // BUG: CLOSED + RECV_SYNACK -> ESTABLISHED, skipping the handshake
        }
        if next == 1 {
            seen_syn_sent = 1;
        }
        state = next;
        if state == 2 {
            assert!(seen_syn_sent == 1);
        }
        i += 1;
    }
    state
}

// ---- Lean-cert coverage (the moat metric) over the safe FSM cases --------------

/// Lean-cert coverage of the safe *protocol-FSM* proofs. Honestly reported, not
/// asserted at a fixed value (FSM/loop refutations route through DRAT today, not
/// the kernel Lean fragment); the soundness floor is asserted. See
/// `network_examples::network_lean_cert_coverage` for the rationale.
#[test]
fn fsm_lean_cert_coverage() {
    let verdicts = vec![
        handshake_validity_safe__axeyum_verdict(),
        handshake_ordering_safe__axeyum_verdict(),
    ];
    let cov = cert_coverage(&verdicts);
    eprintln!(
        "protocol-FSM safe-case Lean-cert coverage: {}/{} carry a Lean module ({:.0}%); \
         {}/{} re-checked their in-tree certificate.",
        cov.lean_certified,
        cov.verified,
        cov.lean_fraction() * 100.0,
        cov.certified,
        cov.verified,
    );
    for v in &verdicts {
        if let Verdict::Verified {
            lean_module: Some(m),
            ..
        } = v
        {
            assert!(
                m.contains("theorem axeyum_refutation") && m.contains("False"),
                "a produced Lean module must be the real refutation module"
            );
        }
    }
    assert_eq!(cov.verified, 2, "both safe FSM cases must verify");
    assert!(cov.lean_certified <= cov.verified);
    assert!((0.0..=1.0).contains(&cov.lean_fraction()));
}
