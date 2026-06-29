//! `BYTE` (0x1a) with a concrete index is now modeled precisely (was havoc'd to a
//! sound `Unknown` before). `BYTE(i, x)` = the i-th byte of x from the most
//! significant; the symbolic model matches the concrete oracle's
//! `to_be_bytes()[i]`, so bugs gated on a byte extraction are found with a
//! replay-validated witness and byte-using safe contracts prove safe.

use axeyum_evm::{AnalyzeConfig, FindingKind, Verdict, analyze};

const STOP: u8 = 0x00;
const CALLDATALOAD: u8 = 0x35;
const BYTE: u8 = 0x1a;
const ISZERO: u8 = 0x15;
const POP: u8 = 0x50;
const JUMPI: u8 = 0x57;
const JUMPDEST: u8 = 0x5b;
const PUSH1: u8 = 0x60;
const REVERT: u8 = 0xfd;

#[test]
fn revert_gated_on_byte_extraction_is_found_and_validated() {
    // x = calldataload(0); if byte(0, x) == 0 { revert } — reachable (the first
    // calldata byte can be zero). Before: BYTE havoc'd → Unknown.
    #[rustfmt::skip]
    let bytecode = [
        PUSH1, 0x00, CALLDATALOAD, // 0..2  x = calldata[0..32]
        PUSH1, 0x00, BYTE,         // 3..5  byte(0, x)  (i on top)
        ISZERO,                    // 6     b == 0
        PUSH1, 0x0b, JUMPI,        // 7..9  if b==0 jump to 0x0b
        STOP,                      // 10
        JUMPDEST,                  // 11 (0x0b)
        PUSH1, 0x00, PUSH1, 0x00, REVERT, // 12..16
    ];
    let report = analyze(&bytecode, &AnalyzeConfig::default());
    assert!(
        report.has_findings(),
        "the byte(0,x)==0 branch is reachable and must be found (was Unknown before)"
    );
    assert_eq!(report.findings[0].kind, FindingKind::Revert);
}

#[test]
fn byte_using_safe_contract_is_no_longer_unknown() {
    // byte(0, calldataload(0)); pop; stop — uses BYTE but has no bug. Before:
    // havoc + saw_unknown forced Unknown; now provably safe.
    let bytecode = [PUSH1, 0x00, CALLDATALOAD, PUSH1, 0x00, BYTE, POP, STOP];
    let report = analyze(&bytecode, &AnalyzeConfig::default());
    assert!(!report.has_findings());
    assert!(
        matches!(report.verdict, Some(Verdict::SafeUpToBound { .. })),
        "a safe BYTE-using contract must now prove safe, got {:?}",
        report.verdict
    );
}
