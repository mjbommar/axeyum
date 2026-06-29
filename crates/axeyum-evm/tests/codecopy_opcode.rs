//! `CODECOPY` (0x39) is modeled precisely (the contract's own code is concrete)
//! for a concrete, 32-aligned, bounded copy — was `Unsupported` → `Unknown`.
//! Branches on copied-then-loaded code bytes are decided deterministically (a
//! wrong/zero copy would flip the verdict).

use axeyum_evm::{AnalyzeConfig, FindingKind, Verdict, analyze};

const STOP: u8 = 0x00;
const CODECOPY: u8 = 0x39;
const MLOAD: u8 = 0x51;
const POP: u8 = 0x50;
const JUMPI: u8 = 0x57;
const JUMPDEST: u8 = 0x5b;
const PUSH1: u8 = 0x60;
const REVERT: u8 = 0xfd;

#[test]
fn revert_on_copied_code_word_is_found() {
    // codecopy(0,0,32); r = mload(0); if (r != 0) revert. The first 32 code bytes
    // start with 0x60 (PUSH1), so r != 0 always — an unconditional revert that is
    // only detectable if CODECOPY copies the real (nonzero) code.
    #[rustfmt::skip]
    let bytecode = [
        PUSH1, 0x20, PUSH1, 0x00, PUSH1, 0x00, CODECOPY, // 0..6  copy code[0..32]→mem[0]
        PUSH1, 0x00, MLOAD,        // 7..9   r = mload(0)
        PUSH1, 0x0e, JUMPI,        // 10..12 if r != 0 jump 0x0e
        STOP,                      // 13
        JUMPDEST,                  // 14 (0x0e)
        PUSH1, 0x00, PUSH1, 0x00, REVERT, // 15..19
    ];
    let report = analyze(&bytecode, &AnalyzeConfig::default());
    assert!(
        report.has_findings(),
        "the copied code word is nonzero, so the revert is reachable (was Unknown before CODECOPY)"
    );
    assert_eq!(report.findings[0].kind, FindingKind::Revert);
}

#[test]
fn codecopy_safe_contract_is_no_longer_unknown() {
    let bytecode = [
        PUSH1, 0x20, PUSH1, 0x00, PUSH1, 0x00, CODECOPY, PUSH1, 0x00, MLOAD, POP, STOP,
    ];
    let report = analyze(&bytecode, &AnalyzeConfig::default());
    assert!(!report.has_findings());
    assert!(
        matches!(report.verdict, Some(Verdict::SafeUpToBound { .. })),
        "a safe CODECOPY-using contract must prove safe, got {:?}",
        report.verdict
    );
}
