//! `EXP` (0x0a) with concrete operands is constant-folded to `base**exp mod
//! 2^256` (was `Op::Unsupported` → `Unknown`). Both interpreters share
//! `Word::pow`, so the fold matches the concrete oracle. A symbolic base/exponent
//! still havocs (sound `Unknown`).

use axeyum_evm::{AnalyzeConfig, FindingKind, Verdict, analyze};

const STOP: u8 = 0x00;
const EXP: u8 = 0x0a;
const EQ: u8 = 0x14;
const JUMPI: u8 = 0x57;
const JUMPDEST: u8 = 0x5b;
const PUSH1: u8 = 0x60;
const PUSH2: u8 = 0x61;
const REVERT: u8 = 0xfd;

#[test]
fn concrete_exp_folds_and_drives_a_revert() {
    // 2 ** 8 == 256 is always true, so this contract unconditionally reverts —
    // which is only detectable if EXP folds to exactly 256.
    #[rustfmt::skip]
    let bytecode = [
        PUSH1, 0x08,            // 0..1  exponent = 8 (pushed first → lower)
        PUSH1, 0x02,            // 2..3  base = 2 (top)
        EXP,                    // 4     2 ** 8 = 256
        PUSH2, 0x01, 0x00,      // 5..7  256
        EQ,                     // 8     (2**8 == 256) = 1
        PUSH1, 0x0d, JUMPI,     // 9..11 always jump
        STOP,                   // 12
        JUMPDEST,               // 13 (0x0d)
        PUSH1, 0x00, PUSH1, 0x00, REVERT, // 14..18
    ];
    let report = analyze(&bytecode, &AnalyzeConfig::default());
    assert!(
        report.has_findings(),
        "2**8==256 must fold true and drive the revert (was Unknown before EXP)"
    );
    assert_eq!(report.findings[0].kind, FindingKind::Revert);
}

#[test]
fn concrete_exp_safe_when_value_does_not_match() {
    // 2 ** 8 == 257 is false, so the revert is unreachable → provably safe. This
    // fails (wrongly reverts) if EXP folds to anything but 256.
    #[rustfmt::skip]
    let bytecode = [
        PUSH1, 0x08,            // 0..1  exponent = 8
        PUSH1, 0x02,            // 2..3  base = 2
        EXP,                    // 4     256
        PUSH2, 0x01, 0x01,      // 5..7  257
        EQ,                     // 8     (256 == 257) = 0
        PUSH1, 0x0d, JUMPI,     // 9..11 never jumps
        STOP,                   // 12
        JUMPDEST,               // 13 (0x0d)
        PUSH1, 0x00, PUSH1, 0x00, REVERT, // 14..18
    ];
    let report = analyze(&bytecode, &AnalyzeConfig::default());
    assert!(!report.has_findings(), "256 != 257 → revert unreachable");
    assert!(
        matches!(report.verdict, Some(Verdict::SafeUpToBound { .. })),
        "must prove safe (EXP folded to 256, not 257), got {:?}",
        report.verdict
    );
}
