//! `CREATE` (0xf0) / `CREATE2` (0xf5) are modeled like a re-entrant call: pop the
//! args, push a witnessed new-contract address, and treat post-state storage as
//! adversarial (the deployed constructor may re-enter). Were `Unsupported` →
//! `Unknown`; now factory-pattern contracts explore past the deploy.

use axeyum_evm::{AnalyzeConfig, FindingKind, Verdict, analyze};

const STOP: u8 = 0x00;
const CREATE: u8 = 0xf0;
const ISZERO: u8 = 0x15;
const POP: u8 = 0x50;
const JUMPI: u8 = 0x57;
const JUMPDEST: u8 = 0x5b;
const PUSH1: u8 = 0x60;
const REVERT: u8 = 0xfd;
const SELFDESTRUCT: u8 = 0xff;

#[test]
fn revert_on_failed_create_is_found() {
    // addr = create(0,0,0); if (addr == 0) revert; — a failed deploy (addr 0) is
    // reachable since the address is nondeterministic.
    #[rustfmt::skip]
    let bytecode = [
        PUSH1, 0x00, PUSH1, 0x00, PUSH1, 0x00, // 0..5  length, offset, value
        CREATE,                  // 6     addr = create(...)
        ISZERO,                  // 7     addr == 0
        PUSH1, 0x0c, JUMPI,      // 8..10 if addr==0 jump 0x0c
        STOP,                    // 11
        JUMPDEST,                // 12 (0x0c)
        PUSH1, 0x00, PUSH1, 0x00, REVERT, // 13..17
    ];
    let report = analyze(&bytecode, &AnalyzeConfig::default());
    assert!(
        report.has_findings(),
        "the failed-create branch is reachable and must be found (was Unknown before CREATE)"
    );
    assert_eq!(report.findings[0].kind, FindingKind::Revert);
}

#[test]
fn create_using_safe_contract_is_no_longer_unknown() {
    // create(0,0,0); pop; stop — deploys but has no bug → provably safe.
    let bytecode = [PUSH1, 0x00, PUSH1, 0x00, PUSH1, 0x00, CREATE, POP, STOP];
    let report = analyze(&bytecode, &AnalyzeConfig::default());
    assert!(!report.has_findings());
    assert!(
        matches!(report.verdict, Some(Verdict::SafeUpToBound { .. })),
        "a safe CREATE-using contract must prove safe, got {:?}",
        report.verdict
    );
}

#[test]
fn selfdestruct_halts_cleanly_not_unknown() {
    // push beneficiary; selfdestruct — a clean halt (like STOP), no bug → safe.
    // Was Unsupported → Unknown.
    let bytecode = [PUSH1, 0x00, SELFDESTRUCT];
    let report = analyze(&bytecode, &AnalyzeConfig::default());
    assert!(!report.has_findings());
    assert!(
        matches!(report.verdict, Some(Verdict::SafeUpToBound { .. })),
        "a contract ending in SELFDESTRUCT must prove safe, got {:?}",
        report.verdict
    );
}
