//! `CALL`-family return data is now modeled as *witnessed fresh bytes* written to
//! memory (for a concrete, 32-aligned, bounded return region). Before, any
//! nonzero return length forced `Unknown`; now a branch on the returned data is
//! decided, with a witness that pins the return value and replays in the concrete
//! oracle (DISAGREE = 0). Larger / symbolic-length / unaligned regions stay a
//! sound `Unknown`.

use axeyum_evm::{AnalyzeConfig, FindingKind, Verdict, analyze};

const STOP: u8 = 0x00;
const ISZERO: u8 = 0x15;
const MLOAD: u8 = 0x51;
const POP: u8 = 0x50;
const JUMPI: u8 = 0x57;
const JUMPDEST: u8 = 0x5b;
const PUSH1: u8 = 0x60;
const STATICCALL: u8 = 0xfa;
const REVERT: u8 = 0xfd;

#[test]
fn revert_gated_on_returned_word_is_found_and_validated() {
    // staticcall(...) with retLength=32 into mem[0]; r = mload(0); if (r == 0) revert.
    // The returned word is witnessed/nondeterministic, so r == 0 is reachable.
    #[rustfmt::skip]
    let bytecode = [
        PUSH1, 0x20,            // 0..1  retLength = 32 (bottom)
        PUSH1, 0x00,            // 2..3  retOffset = 0
        PUSH1, 0x00,            // 4..5  argsLength = 0
        PUSH1, 0x00,            // 6..7  argsOffset = 0
        PUSH1, 0x00,            // 8..9  addr = 0
        PUSH1, 0x00,            // 10..11 gas = 0 (top)
        STATICCALL,             // 12     success on stack; mem[0..32] = return data
        POP,                    // 13     drop success flag
        PUSH1, 0x00, MLOAD,     // 14..16 r = mload(0)
        ISZERO,                 // 17     r == 0
        PUSH1, 0x16, JUMPI,     // 18..20 if r==0 jump 0x16
        STOP,                   // 21
        JUMPDEST,               // 22 (0x16)
        PUSH1, 0x00, PUSH1, 0x00, REVERT, // 23..27
    ];
    let report = analyze(&bytecode, &AnalyzeConfig::default());
    assert!(
        report.has_findings(),
        "a revert gated on returned data must be found (was Unknown before return-data modeling)"
    );
    assert_eq!(report.findings[0].kind, FindingKind::Revert);
}

#[test]
fn unmodeled_return_region_stays_unknown_not_wrong_safe() {
    // A symbolic-length return region is not modeled → the path is Unknown, never
    // a wrong `SafeUpToBound`. Here retLength = calldata[0] (symbolic).
    const CALLDATALOAD: u8 = 0x35;
    #[rustfmt::skip]
    let bytecode = [
        PUSH1, 0x00, CALLDATALOAD, // 0..2  retLength = calldata[0] (symbolic)
        PUSH1, 0x00,               // 3..4  retOffset = 0
        PUSH1, 0x00,               // 5..6  argsLength = 0
        PUSH1, 0x00,               // 7..8  argsOffset = 0
        PUSH1, 0x00,               // 9..10 addr
        PUSH1, 0x00,               // 11..12 gas
        STATICCALL,                // 13
        POP, STOP,                 // 14..15
    ];
    let report = analyze(&bytecode, &AnalyzeConfig::default());
    // The contract has no bug, and the unmodeled (symbolic-length) return region
    // means the path is Unknown — never a false bug, and not a claimed proof we
    // did not establish.
    assert!(!report.has_findings(), "no bug exists in this contract");
    assert!(
        !matches!(report.verdict, Some(Verdict::SafeUpToBound { .. })),
        "a symbolic-length return region must stay Unknown, not claim safe; got {:?}",
        report.verdict
    );
}
