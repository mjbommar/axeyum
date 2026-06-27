//! I4b — `MemoryEncoding::WarmArray` decides the symbolic-storage corpus the same
//! way as the frontend `ite`-fold (`MemoryEncoding::IteFold`), proving the warm
//! SMT-array storage path is denotation-equivalent. The cross-encoding agreement
//! is the soundness check: a verdict that differed between encodings would be a
//! real bug in one of them.

use axeyum_evm::{AnalyzeConfig, FindingKind, MemoryEncoding, Verdict, analyze};

const STOP: u8 = 0x00;
const EQ: u8 = 0x14;
const SHA3: u8 = 0x20;
const CALLDATALOAD: u8 = 0x35;
const MSTORE: u8 = 0x52;
const SLOAD: u8 = 0x54;
const SSTORE: u8 = 0x55;
const JUMPI: u8 = 0x57;
const JUMPDEST: u8 = 0x5b;
const PUSH1: u8 = 0x60;
const PUSH2: u8 = 0x61;
const REVERT: u8 = 0xfd;

fn cfg(memory: MemoryEncoding) -> AnalyzeConfig {
    AnalyzeConfig {
        memory,
        ..AnalyzeConfig::default()
    }
}

/// D — symbolic-key storage round-trip: `storage[k]=v; if storage[lk]==0xdead { revert }`.
/// Reachable when `lk == k` and `v == 0xdead`. Both encodings must find the revert.
#[rustfmt::skip]
fn storage_roundtrip() -> Vec<u8> {
    vec![
        PUSH1, 0x20, CALLDATALOAD, PUSH1, 0x00, CALLDATALOAD, SSTORE,
        PUSH1, 0x40, CALLDATALOAD, SLOAD, PUSH2, 0xde, 0xad, EQ,
        PUSH1, 0x13, JUMPI, STOP, JUMPDEST, PUSH1, 0x00, PUSH1, 0x00, REVERT,
    ]
}

/// D-safe — load a cold slot (never written) and compare to the sentinel: a cold
/// slot reads 0, which can never equal `0xdead`, so the revert is unreachable.
#[rustfmt::skip]
fn cold_slot_safe() -> Vec<u8> {
    vec![
        PUSH1, 0x99, SLOAD, PUSH2, 0xde, 0xad, EQ, PUSH1, 0x0b, JUMPI,
        STOP, JUMPDEST, PUSH1, 0x00, PUSH1, 0x00, REVERT,
    ]
}

/// E — keccak-mapping alias: `storage[keccak(k1.0)]=0xdead; if storage[keccak(k2.0)]==0xdead { revert }`.
/// Reachable exactly when `k1 == k2` (keccak injectivity).
#[rustfmt::skip]
fn keccak_alias() -> Vec<u8> {
    vec![
        PUSH1, 0x00, CALLDATALOAD, PUSH1, 0x00, MSTORE, PUSH1, 0x00, PUSH1, 0x20, MSTORE,
        PUSH2, 0xde, 0xad, PUSH1, 0x40, PUSH1, 0x00, SHA3, SSTORE,
        PUSH1, 0x20, CALLDATALOAD, PUSH1, 0x00, MSTORE, PUSH1, 0x40, PUSH1, 0x00, SHA3, SLOAD,
        PUSH2, 0xde, 0xad, EQ, PUSH1, 0x29, JUMPI, STOP, STOP, JUMPDEST,
        PUSH1, 0x00, PUSH1, 0x00, REVERT,
    ]
}

#[test]
fn warm_array_finds_symbolic_storage_revert() {
    let bytecode = storage_roundtrip();
    let report = analyze(&bytecode, &cfg(MemoryEncoding::WarmArray));
    assert!(
        report.has_findings(),
        "warm-array storage revert is reachable"
    );
    assert_eq!(report.findings[0].kind, FindingKind::Revert);
}

#[test]
fn warm_array_proves_cold_slot_safe() {
    let bytecode = cold_slot_safe();
    let report = analyze(&bytecode, &cfg(MemoryEncoding::WarmArray));
    assert!(
        !report.has_findings(),
        "cold slot can never equal the sentinel"
    );
    assert!(
        matches!(report.verdict, Some(Verdict::SafeUpToBound { .. })),
        "warm-array must prove the cold-slot case safe, got {:?}",
        report.verdict
    );
}

#[test]
fn warm_array_finds_keccak_alias_revert() {
    let bytecode = keccak_alias();
    let report = analyze(&bytecode, &cfg(MemoryEncoding::WarmArray));
    assert!(
        report.has_findings(),
        "warm-array keccak alias revert is reachable"
    );
    assert_eq!(report.findings[0].kind, FindingKind::Revert);
}

/// The cross-encoding soundness check: both encodings agree on every case.
#[test]
fn encodings_agree() {
    for bytecode in [storage_roundtrip(), cold_slot_safe(), keccak_alias()] {
        let ite = analyze(&bytecode, &cfg(MemoryEncoding::IteFold));
        let warm = analyze(&bytecode, &cfg(MemoryEncoding::WarmArray));
        assert_eq!(
            ite.has_findings(),
            warm.has_findings(),
            "ite-fold and warm-array disagree on whether a bug exists"
        );
        if ite.has_findings() {
            assert_eq!(
                ite.findings[0].kind, warm.findings[0].kind,
                "bug kind differs"
            );
        }
    }
}
