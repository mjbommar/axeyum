//! Source-bound evidence for the Chapter 15 three-machine XOR reduction.

use std::{fs, path::Path};

use axeyum_machine::xor_reduction::{
    A0_XOR_REDUCTION_BYTES, RV64_XOR_REDUCTION_BYTES, X64_XOR_REDUCTION_BYTES, XorReductionClause,
    XorReductionError, XorReductionPoint, XorReductionPrograms, simulate_xor_reduction,
    simulate_xor_reduction_with_programs,
};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

use crate::EvidenceError;

const SCHEMA: &str = "axeyum.cross-isa.xor-reduction.v1";
const A0_SOURCE: &[u8] = include_bytes!("../../axeyum-machine/src/a0.rs");
const RV64_SOURCE: &[u8] = include_bytes!("../../axeyum-machine/src/rv64.rs");
const X64_SOURCE: &[u8] = include_bytes!("../../axeyum-machine/src/x64.rs");
const RELATION_SOURCE: &[u8] = include_bytes!("../../axeyum-machine/src/xor_reduction.rs");

/// One finite word-list case replayed through all three complete programs.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ThreeMachineXorCase {
    /// Stable diagnostic name.
    pub name: String,
    /// Words in increasing address order.
    pub words: Vec<u64>,
    /// Common terminal XOR fold.
    pub result: u64,
    /// Named relation points in execution order.
    pub points: Vec<String>,
    /// Independently reported clauses checked.
    pub clauses_checked: u64,
    /// Dynamic A0 instruction count.
    pub a0_steps: u64,
    /// Dynamic RV64I instruction count.
    pub rv64_steps: u64,
    /// Dynamic x86-64 instruction count.
    pub x64_steps: u64,
}

/// Replayable source- and byte-bound report.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ThreeMachineXorReport {
    /// Report schema.
    pub schema: String,
    /// SHA-256 of A0 semantics.
    pub a0_implementation_sha256: String,
    /// SHA-256 of RV64I semantics.
    pub rv64_implementation_sha256: String,
    /// SHA-256 of x86-64 semantics.
    pub x64_implementation_sha256: String,
    /// SHA-256 of the typed relation.
    pub relation_implementation_sha256: String,
    /// SHA-256 of the exact A0 bytes.
    pub a0_program_sha256: String,
    /// SHA-256 of the exact RV64I bytes.
    pub rv64_program_sha256: String,
    /// SHA-256 of the exact x86-64 bytes.
    pub x64_program_sha256: String,
    /// Static A0 instruction count.
    pub a0_static_instructions: u64,
    /// Static RV64I instruction count.
    pub rv64_static_instructions: u64,
    /// Static x86-64 instruction count.
    pub x64_static_instructions: u64,
    /// Interpretation boundary for retained costs.
    pub cost_scope: String,
    /// Exact finite computation scope.
    pub scope: String,
    /// Replayed cases.
    pub cases: Vec<ThreeMachineXorCase>,
    /// Whether all cases and relations passed.
    pub passed: bool,
    /// SHA-256 over canonical case records.
    pub result_sha256: String,
}

/// Produces the source-bound finite three-machine report.
///
/// # Errors
///
/// Returns a semantic mismatch if any machine or relation fails.
pub fn three_machine_xor_report() -> Result<ThreeMachineXorReport, EvidenceError> {
    let cases = [
        ("empty", Vec::new()),
        ("zero", vec![0]),
        ("all-ones", vec![u64::MAX]),
        ("high-bit", vec![0x8000_0000_0000_0000]),
        ("endian-sensitive", vec![0x0102_0304_0506_0708]),
        (
            "cancellation",
            vec![0xfeed_face_cafe_beef, 0xfeed_face_cafe_beef],
        ),
        ("overlapping-bits", vec![0x0f0f, 0x00ff]),
        ("three-word", vec![0, u64::MAX, 0x8000_0000_0000_0000]),
    ]
    .into_iter()
    .map(|(name, words)| case_for(name, words))
    .collect::<Result<Vec<_>, _>>()?;
    let result_sha256 = sha256_hex(&serde_json::to_vec(&cases)?);
    Ok(ThreeMachineXorReport {
        schema: SCHEMA.to_owned(),
        a0_implementation_sha256: sha256_hex(A0_SOURCE),
        rv64_implementation_sha256: sha256_hex(RV64_SOURCE),
        x64_implementation_sha256: sha256_hex(X64_SOURCE),
        relation_implementation_sha256: sha256_hex(RELATION_SOURCE),
        a0_program_sha256: sha256_hex(&A0_XOR_REDUCTION_BYTES),
        rv64_program_sha256: sha256_hex(&RV64_XOR_REDUCTION_BYTES),
        x64_program_sha256: sha256_hex(&X64_XOR_REDUCTION_BYTES),
        a0_static_instructions: 11,
        rv64_static_instructions: 9,
        x64_static_instructions: 8,
        cost_scope: "exact static bytes and instructions plus concrete dynamic instruction counts; descriptive accounting only, with no optimization or minimality claim"
            .to_owned(),
        scope: "eight declared finite word lists of length zero through three; exact Chapter 15 A0, RV64I, and x86-64 bytes; concrete 64-bit execution and typed cut-point relations"
            .to_owned(),
        cases,
        passed: true,
        result_sha256,
    })
}

/// Recomputes every case and compares the complete report.
///
/// # Errors
///
/// Returns a semantic mismatch for malformed, stale, or changed evidence.
pub fn check_three_machine_xor(report_path: &Path) -> Result<ThreeMachineXorReport, EvidenceError> {
    let saved: ThreeMachineXorReport = serde_json::from_slice(&fs::read(report_path)?)?;
    let expected = three_machine_xor_report()?;
    if saved != expected {
        return Err(EvidenceError::SemanticMismatch(
            "three-machine XOR report differs from complete replay".to_owned(),
        ));
    }
    Ok(saved)
}

/// Changes RV64I's pointer step from eight to one and requires rejection.
///
/// # Errors
///
/// Returns a semantic mismatch when the pointer clause rejects the mutation
/// at the second loop head, or a control failure for any other result.
pub fn check_three_machine_xor_pointer_control(report_path: &Path) -> Result<(), EvidenceError> {
    check_three_machine_xor(report_path)?;
    let programs = XorReductionPrograms::with_rv64_pointer_step(1).map_err(machine_error)?;
    match simulate_xor_reduction_with_programs(&[0x0f0f, 0x00ff], &programs) {
        Err(XorReductionError::FailedClause {
            point: XorReductionPoint::LoopHead { iteration: 1 },
            clause: XorReductionClause::Pointer,
        }) => Err(EvidenceError::SemanticMismatch(
            "mutated RV64I pointer step was rejected at the second loop head".to_owned(),
        )),
        Err(error) => Err(EvidenceError::ControlFailure(format!(
            "pointer mutation failed for the wrong reason: {error:?}"
        ))),
        Ok(_) => Err(EvidenceError::ControlFailure(
            "mutated RV64I pointer step satisfied the relation".to_owned(),
        )),
    }
}

fn case_for(name: &str, words: Vec<u64>) -> Result<ThreeMachineXorCase, EvidenceError> {
    let simulation = simulate_xor_reduction(&words).map_err(machine_error)?;
    let points = simulation
        .snapshots
        .iter()
        .map(|snapshot| point_name(snapshot.relation.point))
        .collect();
    let clauses_checked = simulation
        .snapshots
        .iter()
        .map(|snapshot| snapshot.relation.clauses.len() as u64)
        .sum();
    Ok(ThreeMachineXorCase {
        name: name.to_owned(),
        words,
        result: simulation.expected,
        points,
        clauses_checked,
        a0_steps: simulation.a0_steps,
        rv64_steps: simulation.rv64_steps,
        x64_steps: simulation.x64_steps,
    })
}

fn point_name(point: XorReductionPoint) -> String {
    match point {
        XorReductionPoint::Entry => "entry".to_owned(),
        XorReductionPoint::LoopHead { iteration } => format!("loop-head-{iteration}"),
        XorReductionPoint::AfterCombine { iteration } => format!("after-combine-{iteration}"),
        XorReductionPoint::Terminal => "terminal".to_owned(),
    }
}

fn machine_error(error: impl core::fmt::Debug) -> EvidenceError {
    EvidenceError::SemanticMismatch(format!("{error:?}"))
}

fn sha256_hex(bytes: &[u8]) -> String {
    let digest = Sha256::digest(bytes);
    let mut output = String::with_capacity(digest.len() * 2);
    for byte in digest {
        use core::fmt::Write as _;
        write!(&mut output, "{byte:02x}").expect("writing to String cannot fail");
    }
    output
}
