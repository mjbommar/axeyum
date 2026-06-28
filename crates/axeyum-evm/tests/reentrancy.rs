//! A2.3 — re-entrancy: after a may-reenter external call, our storage is treated
//! as adversarial (the callee may have changed any slot), so a storage invariant
//! that held before the call can be violated after it. `STATICCALL` is read-only
//! and does not dirty storage.

use axeyum_evm::{AnalyzeConfig, FindingKind, Verdict, analyze};

const STOP: u8 = 0x00;
const POP: u8 = 0x50;
const SLOAD: u8 = 0x54;
const JUMPI: u8 = 0x57;
const JUMPDEST: u8 = 0x5b;
const PUSH1: u8 = 0x60;
const REVERT: u8 = 0xfd;
const CALL: u8 = 0xf1;
const STATICCALL: u8 = 0xfa;

/// `call(...); x = storage[0]; if (x != 0) revert;`. The slot is cold (0) before
/// the call, so without re-entrancy modeling this is "safe"; with it, the call
/// may have set the slot, so the revert is reachable. `call_op` chooses the call
/// kind; `n_args` its stack arity.
fn after_call_check(call_op: u8, n_args: usize) -> Vec<u8> {
    let mut code = Vec::new();
    for _ in 0..n_args {
        code.extend_from_slice(&[PUSH1, 0x00]); // call args
    }
    code.push(call_op);
    code.push(POP); // drop success
    code.extend_from_slice(&[PUSH1, 0x00, SLOAD]); // x = storage[0]
    // JUMPDEST lands right after the 4-byte `PUSH1 dest JUMPI STOP` sequence.
    let dest = u8::try_from(code.len() + 4).expect("offset fits");
    code.extend_from_slice(&[PUSH1, dest, JUMPI, STOP]); // if x != 0 goto revert
    code.extend_from_slice(&[JUMPDEST, PUSH1, 0x00, PUSH1, 0x00, REVERT]);
    code
}

#[test]
fn reentrancy_invalidates_storage_invariant() {
    // CALL (0xf1, 7 args) may re-enter → storage[0] is adversarial after it.
    let report = analyze(&after_call_check(CALL, 7), &AnalyzeConfig::default());
    assert!(
        report.has_findings(),
        "the post-call storage revert is reachable under re-entrancy"
    );
    assert_eq!(report.findings[0].kind, FindingKind::Revert);
}

#[test]
fn staticcall_does_not_dirty_storage() {
    // STATICCALL (0xfa, 6 args) is read-only → storage[0] stays cold (0) → the
    // revert is unreachable → provably safe.
    let report = analyze(&after_call_check(STATICCALL, 6), &AnalyzeConfig::default());
    assert!(!report.has_findings());
    assert!(
        matches!(report.verdict, Some(Verdict::SafeUpToBound { .. })),
        "a static call must not dirty storage, got {:?}",
        report.verdict
    );
}
