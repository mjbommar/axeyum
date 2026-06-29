//! `LOG0`–`LOG4` (0xa0–0xa4) are modeled as no-op pops: logs are observable side
//! effects with no effect on execution state. Before, a LOG was `Unsupported` and
//! terminated the path as `Unknown`, hiding any bug *after* the log — real
//! contracts emit events constantly, so this was a major false-Unknown source.

use axeyum_evm::{AnalyzeConfig, FindingKind, Verdict, analyze};

const STOP: u8 = 0x00;
const CALLDATALOAD: u8 = 0x35;
const ISZERO: u8 = 0x15;
const JUMPI: u8 = 0x57;
const JUMPDEST: u8 = 0x5b;
const PUSH1: u8 = 0x60;
const LOG0: u8 = 0xa0;
const REVERT: u8 = 0xfd;

#[test]
fn bug_after_a_log_is_found() {
    // LOG0(0,0); if calldata[0] == 0 { revert }. The revert sits *after* the log,
    // so before LOG modeling it was unreachable-as-Unknown; now it's found.
    #[rustfmt::skip]
    let bytecode = [
        PUSH1, 0x00, PUSH1, 0x00, LOG0, // 0..4  LOG0(offset=0, length=0)
        PUSH1, 0x00, CALLDATALOAD,      // 5..7  x = calldata[0]
        ISZERO,                         // 8     x == 0
        PUSH1, 0x0d, JUMPI,             // 9..11 if x==0 jump 0x0d
        STOP,                           // 12
        JUMPDEST,                       // 13 (0x0d)
        PUSH1, 0x00, PUSH1, 0x00, REVERT, // 14..18
    ];
    let report = analyze(&bytecode, &AnalyzeConfig::default());
    assert!(
        report.has_findings(),
        "the revert after LOG0 is reachable and must be found (was Unknown before LOG modeling)"
    );
    assert_eq!(report.findings[0].kind, FindingKind::Revert);
}

#[test]
fn safe_contract_with_a_log_proves_safe() {
    // LOG0(0,0); stop — a logging contract with no bug now proves safe (was
    // Unknown because the LOG terminated the path).
    let bytecode = [PUSH1, 0x00, PUSH1, 0x00, LOG0, STOP];
    let report = analyze(&bytecode, &AnalyzeConfig::default());
    assert!(!report.has_findings());
    assert!(
        matches!(report.verdict, Some(Verdict::SafeUpToBound { .. })),
        "a safe logging contract must prove safe, got {:?}",
        report.verdict
    );
}
