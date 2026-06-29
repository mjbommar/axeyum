//! `SIGNEXTEND` (0x0b) with a concrete byte index is now modeled precisely (was
//! `Op::Unsupported` → `Unknown`). `SIGNEXTEND(b, x)` sign-extends x from a
//! (b+1)-byte two's-complement value; the symbolic `extract`+`sign_ext` model
//! matches the concrete oracle's byte-fill, so signed-overflow / sign-gated
//! branches after it are decided with a replay-validated witness.

use axeyum_evm::{AnalyzeConfig, FindingKind, Verdict, analyze};

const STOP: u8 = 0x00;
const SIGNEXTEND: u8 = 0x0b;
const SLT: u8 = 0x12;
const CALLDATALOAD: u8 = 0x35;
const POP: u8 = 0x50;
const JUMPI: u8 = 0x57;
const JUMPDEST: u8 = 0x5b;
const PUSH1: u8 = 0x60;
const REVERT: u8 = 0xfd;

#[test]
fn revert_gated_on_signextend_sign_is_found() {
    // r = signextend(0, calldataload(0));  if (r <s 0) revert;
    // Reachable: when the low byte's high bit is set, r is negative.
    #[rustfmt::skip]
    let bytecode = [
        PUSH1, 0x00,                 // 0..1  zero (comparison rhs, stays low)
        PUSH1, 0x00, CALLDATALOAD,   // 2..4  x = calldata[0..32]   -> [0, x]
        PUSH1, 0x00, SIGNEXTEND,     // 5..7  signextend(0, x)       -> [0, r]
        SLT,                         // 8     r <s 0
        PUSH1, 0x0d, JUMPI,          // 9..11 if (r <s 0) jump 0x0d
        STOP,                        // 12
        JUMPDEST,                    // 13 (0x0d)
        PUSH1, 0x00, PUSH1, 0x00, REVERT, // 14..18
    ];
    let report = analyze(&bytecode, &AnalyzeConfig::default());
    assert!(
        report.has_findings(),
        "the r<s0 branch after SIGNEXTEND is reachable and must be found (was Unknown before)"
    );
    assert_eq!(report.findings[0].kind, FindingKind::Revert);
}

#[test]
fn symbolic_index_signextend_is_decided_with_valid_witness() {
    // b = calldata[0], x = calldata[32]; r = signextend(b, x); if (r <s 0) revert.
    // The byte index is symbolic, exercising the bounded 31-way `ite`; the
    // reported witness is auto-revalidated (concrete must match the model).
    #[rustfmt::skip]
    let bytecode = [
        PUSH1, 0x00,                 // 0..1  zero (comparison rhs)
        PUSH1, 0x20, CALLDATALOAD,   // 2..4  x = calldata[32:64]   -> [0, x]
        PUSH1, 0x00, CALLDATALOAD,   // 5..7  b = calldata[0:32]     -> [0, x, b]
        SIGNEXTEND,                  // 8     signextend(b, x)        -> [0, r]
        SLT,                         // 9     r <s 0
        PUSH1, 0x0e, JUMPI,          // 10..12 if (r <s 0) jump 0x0e
        STOP,                        // 13
        JUMPDEST,                    // 14 (0x0e)
        PUSH1, 0x00, PUSH1, 0x00, REVERT, // 15..19
    ];
    let report = analyze(&bytecode, &AnalyzeConfig::default());
    assert!(
        report.has_findings(),
        "a negative signextend result is reachable and must be found with a valid witness"
    );
    assert_eq!(report.findings[0].kind, FindingKind::Revert);
}

#[test]
fn signextend_using_safe_contract_is_no_longer_unknown() {
    // signextend(0, calldataload(0)); pop; stop — uses SIGNEXTEND but has no bug.
    let bytecode = [
        PUSH1,
        0x00,
        CALLDATALOAD,
        PUSH1,
        0x00,
        SIGNEXTEND,
        POP,
        STOP,
    ];
    let report = analyze(&bytecode, &AnalyzeConfig::default());
    assert!(!report.has_findings());
    assert!(
        matches!(report.verdict, Some(Verdict::SafeUpToBound { .. })),
        "a safe SIGNEXTEND-using contract must now prove safe, got {:?}",
        report.verdict
    );
}
