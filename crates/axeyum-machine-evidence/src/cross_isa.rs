//! Source-bound evidence for the typed three-machine absolute-value relation.

use std::{fs, path::Path};

use axeyum_machine::{
    cross_isa::{
        AbsoluteValuePoint, AbsoluteValuePrograms, RelationError, simulate_absolute_value,
        simulate_absolute_value_with_programs,
    },
    x64,
};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

use crate::EvidenceError;

const SCHEMA: &str = "axeyum.cross-isa.absolute-value.v1";
const A0_SOURCE: &[u8] = include_bytes!("../../axeyum-machine/src/a0.rs");
const RV64_SOURCE: &[u8] = include_bytes!("../../axeyum-machine/src/rv64.rs");
const X64_SOURCE: &[u8] = include_bytes!("../../axeyum-machine/src/x64.rs");
const RELATION_SOURCE: &[u8] = include_bytes!("../../axeyum-machine/src/cross_isa.rs");

/// One concrete input replayed through all three semantics and relations.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct AbsoluteValueCase {
    /// Common 64-bit input word.
    pub input: u64,
    /// `keep` for nonnegative inputs and `negate` otherwise.
    pub path: String,
    /// Common modular result at all three exits.
    pub result: u64,
    /// Named synchronization points checked in execution order.
    pub points: Vec<String>,
    /// Number of independently reported relation clauses checked.
    pub clauses_checked: u64,
    /// Whether the mathematical-positive interpretation admits this input.
    pub mathematical_absolute_value_admitted: bool,
}

/// Replayable finite-domain report for the first typed cross-ISA relation.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CrossIsaAbsoluteValueReport {
    /// Report schema.
    pub schema: String,
    /// SHA-256 of the compiled A0 semantic source.
    pub a0_implementation_sha256: String,
    /// SHA-256 of the compiled RV64I semantic source.
    pub rv64_implementation_sha256: String,
    /// SHA-256 of the compiled x86-64 semantic source.
    pub x64_implementation_sha256: String,
    /// SHA-256 of the typed relation implementation.
    pub relation_implementation_sha256: String,
    /// Exact scope of the computation.
    pub scope: String,
    /// Boundary and branch-shape cases replayed.
    pub cases: Vec<AbsoluteValueCase>,
    /// Whether every case reached every applicable point with all clauses true.
    pub passed: bool,
    /// SHA-256 over the canonical case records.
    pub result_sha256: String,
}

/// Produces the source-bound cross-ISA absolute-value computation.
///
/// # Errors
///
/// Returns a semantic mismatch if any concrete machine or relation fails.
pub fn cross_isa_absolute_value_report() -> Result<CrossIsaAbsoluteValueReport, EvidenceError> {
    let inputs = [
        0,
        1,
        7,
        0x0000_0000_ffff_ffff,
        i64::MAX.cast_unsigned(),
        i64::MIN.cast_unsigned(),
        (-1_i64).cast_unsigned(),
        (-7_i64).cast_unsigned(),
        0xffff_ffff_0000_0000,
        0x8000_0000_0000_0001,
    ];
    let cases = inputs
        .into_iter()
        .map(case_for)
        .collect::<Result<Vec<_>, _>>()?;
    let case_bytes = serde_json::to_vec(&cases)?;
    Ok(CrossIsaAbsoluteValueReport {
        schema: SCHEMA.to_owned(),
        a0_implementation_sha256: sha256_hex(A0_SOURCE),
        rv64_implementation_sha256: sha256_hex(RV64_SOURCE),
        x64_implementation_sha256: sha256_hex(X64_SOURCE),
        relation_implementation_sha256: sha256_hex(RELATION_SOURCE),
        scope: "ten declared 64-bit boundary and branch-shape inputs; concrete modular absolute value; mathematical-positive interpretation excludes signed minimum"
            .to_owned(),
        cases,
        passed: true,
        result_sha256: sha256_hex(&case_bytes),
    })
}

/// Recomputes and checks the cross-ISA absolute-value report.
///
/// # Errors
///
/// Returns `semantic-mismatch` for malformed, stale, or changed evidence.
pub fn check_cross_isa_absolute_value(
    report_path: &Path,
) -> Result<CrossIsaAbsoluteValueReport, EvidenceError> {
    let saved: CrossIsaAbsoluteValueReport = serde_json::from_slice(&fs::read(report_path)?)?;
    let expected = cross_isa_absolute_value_report()?;
    if saved != expected {
        return Err(EvidenceError::SemanticMismatch(
            "cross-ISA absolute-value report differs from replay".to_owned(),
        ));
    }
    Ok(saved)
}

/// Changes x86 `jns` to `je` and requires the shared relation to reject it.
///
/// # Errors
///
/// Returns `semantic-mismatch` when the predicate mutation is distinguished
/// and `control-failure` if the faulty program is accepted.
pub fn check_cross_isa_predicate_control(report_path: &Path) -> Result<(), EvidenceError> {
    check_cross_isa_absolute_value(report_path)?;
    let canonical = AbsoluteValuePrograms::book().map_err(machine_error)?;
    let mutated = AbsoluteValuePrograms {
        a0: canonical.a0,
        rv64: canonical.rv64,
        x64: x64::Program::new(
            0,
            vec![
                0x48, 0x89, 0xf8, 0x48, 0x85, 0xc0, 0x74, 0x03, 0x48, 0xf7, 0xd8,
            ],
        ),
    };
    match simulate_absolute_value_with_programs(7, &mutated) {
        Err(RelationError::FailedClause {
            point: AbsoluteValuePoint::Exit,
            clause: axeyum_machine::cross_isa::RelationClause::ControlPoint,
        }) => Err(EvidenceError::SemanticMismatch(
            "mutated x86 signed predicate was rejected at the exit movement".to_owned(),
        )),
        Err(error) => Err(EvidenceError::ControlFailure(format!(
            "predicate mutation failed for the wrong reason: {error:?}"
        ))),
        Ok(_) => Err(EvidenceError::ControlFailure(
            "mutated x86 signed predicate satisfied the relation".to_owned(),
        )),
    }
}

fn case_for(input: u64) -> Result<AbsoluteValueCase, EvidenceError> {
    let simulation = simulate_absolute_value(input).map_err(machine_error)?;
    let result = simulation.exit.a0.registers[0].unsigned();
    if simulation.exit.rv64.register(10) != result || simulation.exit.x64.register(0) != result {
        return Err(EvidenceError::SemanticMismatch(
            "exit results disagree after a passing relation".to_owned(),
        ));
    }
    let points = simulation
        .relations
        .iter()
        .map(|relation| point_name(relation.point).to_owned())
        .collect();
    let clauses_checked = simulation
        .relations
        .iter()
        .map(|relation| u64::try_from(relation.clauses.len()).expect("small clause suite"))
        .sum();
    Ok(AbsoluteValueCase {
        input,
        path: if input.cast_signed() >= 0 {
            "keep"
        } else {
            "negate"
        }
        .to_owned(),
        result,
        points,
        clauses_checked,
        mathematical_absolute_value_admitted: input != i64::MIN.cast_unsigned(),
    })
}

const fn point_name(point: AbsoluteValuePoint) -> &'static str {
    match point {
        AbsoluteValuePoint::Entry => "entry",
        AbsoluteValuePoint::Decision => "decision",
        AbsoluteValuePoint::Update => "update",
        AbsoluteValuePoint::Exit => "exit",
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
