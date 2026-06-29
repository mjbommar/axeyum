//! Adversarial differential fuzz for the EVM bug-hunter — the soundness floor
//! (`DISAGREE = 0`) stress-tested over many random programs.
//!
//! The core invariant: if a *concrete* run of a random program on random calldata
//! reaches a `REVERT`/`INVALID` (a real reachable bug), then `analyze` of that
//! program must **never** return `SafeUpToBound` — it must report a bug or an
//! honest `Unknown`. A `SafeUpToBound` in that situation would be a wrong "no bug"
//! (the EVM analog of a wrong `unsat`). The witness exists by construction (the
//! concrete calldata), so the symbolic analysis must not claim safety.
//!
//! Deterministic (fixed-seed LCG), no external crates.
#![allow(clippy::cast_possible_truncation)] // intentional in the PRNG / index math

use axeyum_evm::concrete::{self, Env, Halt};
use axeyum_evm::opcode::decode;
use axeyum_evm::word::Word;
use axeyum_evm::{AnalyzeConfig, analyze};

/// A tiny deterministic PRNG (SplitMix-ish LCG) — reproducible fuzzing.
struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        self.0 ^ (self.0 >> 31)
    }
    fn byte_from(&mut self, pool: &[u8]) -> u8 {
        pool[(self.next() as usize) % pool.len()]
    }
    fn range(&mut self, lo: usize, hi: usize) -> usize {
        lo + (self.next() as usize) % (hi - lo)
    }
}

/// Opcode pool: a curated mix that produces interesting control flow + reverts.
/// `MUL` (0x02) is excluded — 256-bit `bv_umulo` bit-blast is too slow for a fuzz.
const POOL: &[u8] = &[
    0x00, 0x01, 0x03, 0x10, 0x11, 0x14, 0x15, 0x16,
    0x17, // STOP ADD SUB LT GT EQ ISZERO AND OR
    0x35, 0x51, 0x52, 0x50, 0x56, 0x57,
    0x5b, // CALLDATALOAD MLOAD MSTORE POP JUMP JUMPI JUMPDEST
    0x1a, // BYTE — exercise the concrete/symbolic-index byte-extraction paths
    0x54, 0x55, // SLOAD SSTORE — exercise the storage paths
    0x31, 0x5a, // BALANCE GAS — exercise the environment paths
    0xf1, 0xfa, // CALL STATICCALL — exercise the external-call paths
    0x60, 0x61, 0x80, 0x90, // PUSH1 PUSH2 DUP1 SWAP1
    0xf3, 0xfd, 0xfe, // RETURN REVERT INVALID
    0x00, 0xff, 0x0a, 0x20, // some data/immediate bytes
];

const STEPS: usize = 1_000;

#[test]
fn concrete_reachable_bug_is_never_reported_safe() {
    let mut rng = Rng(0x5eed_1234_abcd_0001);
    let mut checked_reverting = 0u32;
    for _ in 0..400 {
        let len = rng.range(4, 18);
        let bytecode: Vec<u8> = (0..len).map(|_| rng.byte_from(POOL)).collect();
        let calldata: Vec<u8> = (0..64).map(|_| (rng.next() & 0xff) as u8).collect();

        let program = decode(&bytecode);
        let env = Env {
            calldata: calldata.clone(),
            callvalue: Word::zero(),
            caller: Word::zero(),
        };
        let halt = concrete::run(&program, &env, STEPS);
        if !matches!(halt, Halt::Revert(_) | Halt::Invalid) {
            continue;
        }
        checked_reverting += 1;

        // A concrete input reaches a bug → the symbolic analysis must not claim
        // safety. Bug-found or Unknown are both sound; SafeUpToBound is not.
        let report = analyze(
            &bytecode,
            &AnalyzeConfig {
                max_steps: STEPS,
                ..AnalyzeConfig::default()
            },
        );
        let claimed_safe = matches!(
            report.verdict,
            Some(axeyum_evm::Verdict::SafeUpToBound { .. })
        ) && !report.has_findings();
        assert!(
            !claimed_safe,
            "wrong-safe: concrete halt {halt:?} is reachable but analyze proved \
             SafeUpToBound for bytecode {bytecode:02x?} (calldata {calldata:02x?})"
        );
    }
    // The corpus must actually exercise the invariant (not vacuously pass).
    assert!(
        checked_reverting >= 5,
        "fuzz did not generate enough reverting programs ({checked_reverting})"
    );
}

#[test]
fn concrete_reachable_bug_across_two_txs_is_never_reported_safe() {
    // The multi-tx analog: if a two-call concrete sequence (storage persisting)
    // reaches a bug, analyze with max_txs=2 must not prove SafeUpToBound.
    let mut rng = Rng(0xb167_0000_0000_0003);
    let mut checked = 0u32;
    for _ in 0..300 {
        let len = rng.range(4, 16);
        let bytecode: Vec<u8> = (0..len).map(|_| rng.byte_from(POOL)).collect();
        let mk_env = |rng: &mut Rng| Env {
            calldata: (0..64).map(|_| (rng.next() & 0xff) as u8).collect(),
            callvalue: Word::zero(),
            caller: Word::zero(),
        };
        let e1 = mk_env(&mut rng);
        let e2 = mk_env(&mut rng);
        let program = decode(&bytecode);
        let halt = concrete::run_sequence(&program, &[e1, e2], STEPS, &[]);
        if !matches!(halt, Halt::Revert(_) | Halt::Invalid) {
            continue;
        }
        checked += 1;
        let report = analyze(
            &bytecode,
            &AnalyzeConfig {
                max_steps: STEPS,
                max_txs: 2,
                ..AnalyzeConfig::default()
            },
        );
        let claimed_safe = matches!(
            report.verdict,
            Some(axeyum_evm::Verdict::SafeUpToBound { .. })
        ) && !report.has_findings();
        assert!(
            !claimed_safe,
            "wrong-safe (multi-tx): a 2-tx sequence halts {halt:?} but analyze(max_txs=2) \
             proved SafeUpToBound for {bytecode:02x?}"
        );
    }
    assert!(
        checked >= 3,
        "multi-tx fuzz exercised too few reverting sequences ({checked})"
    );
}

#[test]
fn analyze_is_total_on_random_bytecode() {
    // analyze must never panic and always return a well-formed report on arbitrary
    // bytecode (sound totality: a finding xor a verdict).
    let mut rng = Rng(0x000a_11ce_0000_0042);
    for _ in 0..400 {
        let len = rng.range(1, 24);
        let bytecode: Vec<u8> = (0..len).map(|_| rng.byte_from(POOL)).collect();
        let report = analyze(
            &bytecode,
            &AnalyzeConfig {
                max_steps: 500,
                ..AnalyzeConfig::default()
            },
        );
        // Exactly one of: a finding, or a verdict.
        assert_eq!(
            report.has_findings(),
            report.verdict.is_none(),
            "report must carry a finding xor a verdict for {bytecode:02x?}"
        );
        // A reported finding always carries a (revalidated) witness.
        if let Some(f) = report.findings.first() {
            assert!(
                f.calldata_witness.len() <= 256,
                "witness calldata is bounded by the modeled buffer"
            );
        }
    }
}

#[test]
fn ite_fold_and_warm_array_never_contradict() {
    // The two storage encodings are denotation-equivalent: over random programs
    // they must never give *contradictory decided* verdicts (one SafeUpToBound,
    // the other a reported bug). Differing unknown/decided is fine (encodings have
    // different costs); a flat contradiction would be a soundness bug in one.
    use axeyum_evm::MemoryEncoding;
    let mut rng = Rng(0xc0de_a11a_0000_0001);
    let mut checked = 0u32;
    for _ in 0..300 {
        let len = rng.range(4, 16);
        let bytecode: Vec<u8> = (0..len).map(|_| rng.byte_from(POOL)).collect();
        let run = |m: MemoryEncoding| {
            analyze(
                &bytecode,
                &AnalyzeConfig {
                    max_steps: STEPS,
                    memory: m,
                    ..AnalyzeConfig::default()
                },
            )
        };
        let ite = run(MemoryEncoding::IteFold);
        let warm = run(MemoryEncoding::WarmArray);
        let ite_safe = matches!(ite.verdict, Some(axeyum_evm::Verdict::SafeUpToBound { .. }))
            && !ite.has_findings();
        let warm_safe = matches!(
            warm.verdict,
            Some(axeyum_evm::Verdict::SafeUpToBound { .. })
        ) && !warm.has_findings();
        // Contradiction = one proved safe while the other found a bug.
        let contradiction = (ite_safe && warm.has_findings()) || (warm_safe && ite.has_findings());
        assert!(
            !contradiction,
            "encoding contradiction on {bytecode:02x?}: ite_safe={ite_safe} warm_safe={warm_safe} \
             ite_bug={} warm_bug={}",
            ite.has_findings(),
            warm.has_findings()
        );
        if ite_safe || warm_safe || ite.has_findings() || warm.has_findings() {
            checked += 1;
        }
    }
    assert!(
        checked >= 5,
        "encoding-agreement fuzz exercised too few decided programs ({checked})"
    );
}
