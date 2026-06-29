//! `CALLDATACOPY` (0x37) is modeled precisely (the calldata is already symbolic)
//! for a concrete, 32-aligned, bounded copy — was `Unsupported` → `Unknown`.
//! Branches on copied-then-loaded calldata are decided, and the witness replays
//! in the concrete oracle (which copies the real calldata bytes), so DISAGREE=0.

use axeyum_evm::{AnalyzeConfig, FindingKind, Verdict, analyze};

const STOP: u8 = 0x00;
const CALLDATACOPY: u8 = 0x37;
const ISZERO: u8 = 0x15;
const MLOAD: u8 = 0x51;
const POP: u8 = 0x50;
const JUMPI: u8 = 0x57;
const JUMPDEST: u8 = 0x5b;
const PUSH1: u8 = 0x60;
const REVERT: u8 = 0xfd;

#[test]
fn revert_gated_on_copied_calldata_is_found() {
    // calldatacopy(0, 0, 32); r = mload(0); if (r == 0) revert. r equals the first
    // calldata word (precise copy), so r == 0 is reachable.
    #[rustfmt::skip]
    let bytecode = [
        PUSH1, 0x20, PUSH1, 0x00, PUSH1, 0x00, CALLDATACOPY, // 0..6  copy cd[0..32]→mem[0]
        PUSH1, 0x00, MLOAD,         // 7..9   r = mload(0)
        ISZERO,                     // 10     r == 0
        PUSH1, 0x0f, JUMPI,         // 11..13 if r==0 jump 0x0f
        STOP,                       // 14
        JUMPDEST,                   // 15 (0x0f)
        PUSH1, 0x00, PUSH1, 0x00, REVERT, // 16..20
    ];
    let report = analyze(&bytecode, &AnalyzeConfig::default());
    assert!(
        report.has_findings(),
        "a revert gated on copied calldata must be found (was Unknown before CALLDATACOPY)"
    );
    assert_eq!(report.findings[0].kind, FindingKind::Revert);
}

#[test]
fn calldatacopy_safe_contract_is_no_longer_unknown() {
    // calldatacopy(0,0,32); pop-free no-op; stop — uses CALLDATACOPY, no bug.
    let bytecode = [
        PUSH1, 0x20, PUSH1, 0x00, PUSH1, 0x00, CALLDATACOPY, PUSH1, 0x00, MLOAD, POP, STOP,
    ];
    let report = analyze(&bytecode, &AnalyzeConfig::default());
    assert!(!report.has_findings());
    assert!(
        matches!(report.verdict, Some(Verdict::SafeUpToBound { .. })),
        "a safe CALLDATACOPY-using contract must prove safe, got {:?}",
        report.verdict
    );
}
