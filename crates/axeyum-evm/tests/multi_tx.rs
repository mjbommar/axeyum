//! A1.1 — multi-transaction exploration: persistent storage across a call
//! sequence (memory/stack reset per tx, fresh symbolic calldata per tx).
//!
//! The headline case is a *multi-tx-only* bug: a contract that is safe in any
//! single call but whose revert becomes reachable across two calls. This proves
//! the multi-tx driver genuinely expands the reachable state space — while
//! staying sound (a cross-tx witness it cannot yet single-tx-revalidate is
//! reported as honest `Unknown`, never a wrong verdict; the validated multi-tx
//! witness arrives with A1.2/A1.3).

use axeyum_evm::{AnalyzeConfig, FindingKind, Verdict, analyze};

const STOP: u8 = 0x00;
const EQ: u8 = 0x14;
const ISZERO: u8 = 0x15;
const SLOAD: u8 = 0x54;
const SSTORE: u8 = 0x55;
const JUMPI: u8 = 0x57;
const JUMPDEST: u8 = 0x5b;
const PUSH1: u8 = 0x60;
const PUSH2: u8 = 0x61;
const REVERT: u8 = 0xfd;

fn cfg(max_txs: usize) -> AnalyzeConfig {
    AnalyzeConfig {
        max_txs,
        ..AnalyzeConfig::default()
    }
}

/// `if (storage[0] == 0) { storage[0] = 1; } else { revert; }`.
/// First call: slot is cold (0) → sets it to 1, stops (safe).
/// Second call: slot is 1 → reverts. So the revert needs **two** transactions.
#[rustfmt::skip]
fn increment_once_then_revert() -> Vec<u8> {
    vec![
        PUSH1, 0x00, SLOAD, ISZERO, PUSH1, 0x0c, JUMPI, // if storage[0]==0 goto 12
        PUSH1, 0x00, PUSH1, 0x00, REVERT,               // else revert  (offsets 7..11)
        JUMPDEST, PUSH1, 0x01, PUSH1, 0x00, SSTORE, STOP, // 12: storage[0]=1; stop
    ]
}

/// Loads a cold slot (never written) and compares to a sentinel — safe no matter
/// how many times it is called (storage persists but the slot stays 0).
#[rustfmt::skip]
fn cold_slot_safe() -> Vec<u8> {
    vec![
        PUSH1, 0x99, SLOAD, PUSH2, 0xde, 0xad, EQ, PUSH1, 0x0b, JUMPI,
        STOP, JUMPDEST, PUSH1, 0x00, PUSH1, 0x00, REVERT,
    ]
}

#[test]
fn single_tx_proves_increment_contract_safe() {
    // One call can only take the cold (set-to-1) branch: provably safe.
    let report = analyze(&increment_once_then_revert(), &cfg(1));
    assert!(!report.has_findings());
    assert!(
        matches!(report.verdict, Some(Verdict::SafeUpToBound { .. })),
        "single tx is safe, got {:?}",
        report.verdict
    );
}

#[test]
fn two_tx_reports_validated_cross_tx_bug() {
    // Two calls reach the revert (slot is 1 on the second call). With the multi-tx
    // replay oracle (A1.2) + sequence witness (A1.3), this cross-tx bug is now
    // *reported* with a replay-validated 2-tx witness — not just reached.
    let report = analyze(&increment_once_then_revert(), &cfg(2));
    assert!(
        report.has_findings(),
        "the cross-tx revert is now a reported finding"
    );
    let f = &report.findings[0];
    assert_eq!(f.kind, FindingKind::Revert);
    assert_eq!(
        f.prior_txs.len(),
        1,
        "the witness is a 2-tx sequence: one prior tx (sets the slot) then the bug tx"
    );
}

#[test]
fn multi_tx_safe_contract_stays_proved_safe() {
    // A genuinely safe contract stays SafeUpToBound across several transactions.
    let report = analyze(&cold_slot_safe(), &cfg(3));
    assert!(!report.has_findings());
    assert!(
        matches!(report.verdict, Some(Verdict::SafeUpToBound { .. })),
        "safe-under-any-tx-count must prove safe, got {:?}",
        report.verdict
    );
}
