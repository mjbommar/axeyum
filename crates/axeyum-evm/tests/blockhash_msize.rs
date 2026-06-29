//! `BLOCKHASH` (0x40) and `MSIZE` (0x59) route to the witnessed-`Env` path (were
//! `Unsupported` → `Unknown`). BLOCKHASH pops the block number and pushes a
//! nondeterministic (witnessed) hash; MSIZE pushes a witnessed memory size. Paths
//! now explore past them instead of halting.

use axeyum_evm::{AnalyzeConfig, FindingKind, Verdict, analyze};

const STOP: u8 = 0x00;
const ISZERO: u8 = 0x15;
const POP: u8 = 0x50;
const JUMPI: u8 = 0x57;
const MSIZE: u8 = 0x59;
const JUMPDEST: u8 = 0x5b;
const PUSH1: u8 = 0x60;
const BLOCKHASH: u8 = 0x40;
const REVERT: u8 = 0xfd;

#[test]
fn revert_gated_on_blockhash_is_found() {
    // if (blockhash(0) == 0) revert; — reachable (the hash is nondeterministic).
    #[rustfmt::skip]
    let bytecode = [
        PUSH1, 0x00, BLOCKHASH, // 0..2  blockhash(0)
        ISZERO,                 // 3     == 0
        PUSH1, 0x08, JUMPI,     // 4..6  if ==0 jump 0x08
        STOP,                   // 7
        JUMPDEST,               // 8 (0x08)
        PUSH1, 0x00, PUSH1, 0x00, REVERT, // 9..13
    ];
    let report = analyze(&bytecode, &AnalyzeConfig::default());
    assert!(
        report.has_findings(),
        "the blockhash()==0 branch is reachable and must be found (was Unknown before)"
    );
    assert_eq!(report.findings[0].kind, FindingKind::Revert);
}

#[test]
fn msize_using_safe_contract_is_no_longer_unknown() {
    // msize; pop; stop — uses MSIZE but has no bug → provably safe (was Unknown).
    let bytecode = [MSIZE, POP, STOP];
    let report = analyze(&bytecode, &AnalyzeConfig::default());
    assert!(!report.has_findings());
    assert!(
        matches!(report.verdict, Some(Verdict::SafeUpToBound { .. })),
        "a safe MSIZE-using contract must prove safe, got {:?}",
        report.verdict
    );
}
