//! Content-bound evidence producers and replay checkers for machine semantics.
//!
//! This crate consumes `axeyum-machine`; it does not define another machine.
//! Reports bind the exact semantic source digest, declare their finite domain,
//! and are accepted only after the checker recomputes the result.

use std::{fs, path::Path};

use axeyum_machine::a0::{
    Memory, MemorySpan, Observation, Outcome, Program, State, StopReason, Trap, Word, run,
    run_prefix, step,
};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

const A0_SOURCE: &[u8] = include_bytes!("../../axeyum-machine/src/a0.rs");
const PACKAGE_SCHEMA: &str = "axeyum.a0.semantic-package.v3";
const ROUNDTRIP_SCHEMA: &str = "axeyum.a0.word-roundtrip.v1";
const OBSERVATION_SCHEMA: &str = "axeyum.a0.observation-separation.v1";
const ADD_SCHEMA: &str = "axeyum.a0.add-step-exhaustive.v1";
const MEMORY_SCHEMA: &str = "axeyum.a0.memory-trace.v1";
const BRANCH_SCHEMA: &str = "axeyum.a0.branch-trace.v1";
const RUN_SCHEMA: &str = "axeyum.a0.run-classification.v1";

/// Stable metadata that binds evidence to the concrete A0 semantic authority.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct A0SemanticPackage {
    /// Package schema identifier.
    pub schema: String,
    /// Semantic package version.
    pub version: String,
    /// Repository-relative semantic implementation path.
    pub source_path: String,
    /// SHA-256 of the exact semantic implementation source.
    pub source_sha256: String,
    /// Supported architectural word widths.
    pub word_widths: Vec<u8>,
    /// Instruction width in bytes.
    pub instruction_bytes: u8,
    /// Architectural byte order for data words.
    pub byte_order: String,
    /// Implemented semantic surfaces bound by the source digest.
    pub capabilities: Vec<String>,
}

/// Recomputed finite-domain report for A0 byte split/join.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct WordRoundtripReport {
    /// Report schema identifier.
    pub schema: String,
    /// SHA-256 of the canonical semantic-package JSON bytes.
    pub semantic_package_sha256: String,
    /// Exhaustively enumerated word widths.
    pub exhaustive_widths: Vec<u8>,
    /// Number of values enumerated.
    pub values_checked: u64,
    /// Whether every reconstructed word equalled its input.
    pub passed: bool,
    /// SHA-256 of the canonical sequence of checked inputs and outputs.
    pub result_sha256: String,
}

/// Recomputed report for a narrow and broad observation of two complete states.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ObservationSeparationReport {
    /// Report schema identifier.
    pub schema: String,
    /// SHA-256 of the canonical semantic-package JSON bytes.
    pub semantic_package_sha256: String,
    /// SHA-256 of the two complete canonical input states.
    pub witness_states_sha256: String,
    /// Registers retained by the narrow observation.
    pub narrow_registers: Vec<u8>,
    /// Registers retained by the broad observation.
    pub broad_registers: Vec<u8>,
    /// Whether the two narrow observations agree.
    pub narrow_equal: bool,
    /// Whether the two broad observations agree.
    pub broad_equal: bool,
    /// First requested register that separates the broad observations.
    pub separating_register: Option<u8>,
    /// Separating value in the left state.
    pub left_value: Option<u64>,
    /// Separating value in the right state.
    pub right_value: Option<u64>,
}

/// Exhaustive width-8 A0 addition report, including flags and PC.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct AddStepReport {
    /// Report schema identifier.
    pub schema: String,
    /// SHA-256 of the semantic-package JSON bytes.
    pub semantic_package_sha256: String,
    /// Exhaustively checked architectural width.
    pub width: u8,
    /// Destination register inspected by the checker.
    pub destination: u8,
    /// Number of operand pairs checked.
    pub cases_checked: u64,
    /// Whether result, Z/N/C/V, PC, and frame controls matched the oracle.
    pub passed: bool,
    /// SHA-256 over every input and recomputed architectural output.
    pub result_sha256: String,
}

/// Concrete store/load and trapped-boundary report.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct MemoryTraceReport {
    /// Report schema identifier.
    pub schema: String,
    /// SHA-256 of the semantic-package JSON bytes.
    pub semantic_package_sha256: String,
    /// Stored word.
    pub stored_word: u64,
    /// Bytes observed at increasing addresses after store.
    pub stored_bytes: Vec<u8>,
    /// Word recovered by the following load.
    pub loaded_word: u64,
    /// Whether an out-of-range store trapped.
    pub boundary_trapped: bool,
    /// Whether the trapped store left memory unchanged.
    pub no_partial_write: bool,
    /// Program counters from initial, stored, and loaded states.
    pub successful_pcs: Vec<u64>,
}

/// Taken and untaken conditional-branch trace report.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BranchTraceReport {
    /// Report schema identifier.
    pub schema: String,
    /// SHA-256 of the semantic-package JSON bytes.
    pub semantic_package_sha256: String,
    /// PCs in the initial, branched, and halted taken-path states.
    pub taken_pcs: Vec<u64>,
    /// PCs in the initial, branched, and halted untaken-path states.
    pub untaken_pcs: Vec<u64>,
    /// Stop classification for the taken trace.
    pub taken_stop: String,
    /// Stop classification for the untaken trace.
    pub untaken_stop: String,
}

/// Concrete coverage of all four A0 runner classifications and resumption.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct RunClassificationReport {
    /// Report schema identifier.
    pub schema: String,
    /// SHA-256 of the semantic-package JSON bytes.
    pub semantic_package_sha256: String,
    /// Stop label for a normally halted run.
    pub halted_stop: String,
    /// Stop label for an illegal-fetch run.
    pub trapped_stop: String,
    /// Stop label for a bounded running loop.
    pub exhausted_stop: String,
    /// Stop label for a caller-returned running prefix.
    pub prefix_stop: String,
    /// State count for a zero-step bounded run.
    pub zero_bound_states: usize,
    /// Whether two resumed prefixes equal one prefix of their combined length.
    pub resumed_equals_whole: bool,
    /// PCs in the combined five-step prefix.
    pub resumed_pcs: Vec<u64>,
}

/// Why an evidence package or report was rejected.
#[derive(Debug)]
pub enum EvidenceError {
    /// File access failed.
    Io(std::io::Error),
    /// JSON decoding or encoding failed.
    Json(serde_json::Error),
    /// The semantic package does not describe the compiled semantic source.
    SemanticPackageMismatch(String),
    /// Recomputed evidence differs from the claimed report.
    SemanticMismatch(String),
}

impl core::fmt::Display for EvidenceError {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::Io(error) => write!(formatter, "I/O error: {error}"),
            Self::Json(error) => write!(formatter, "JSON error: {error}"),
            Self::SemanticPackageMismatch(detail) => {
                write!(formatter, "semantic-package-mismatch: {detail}")
            }
            Self::SemanticMismatch(detail) => write!(formatter, "semantic-mismatch: {detail}"),
        }
    }
}

impl std::error::Error for EvidenceError {}

impl From<std::io::Error> for EvidenceError {
    fn from(error: std::io::Error) -> Self {
        Self::Io(error)
    }
}

impl From<serde_json::Error> for EvidenceError {
    fn from(error: serde_json::Error) -> Self {
        Self::Json(error)
    }
}

/// Returns metadata for the exact A0 semantics compiled into this checker.
#[must_use]
pub fn semantic_package() -> A0SemanticPackage {
    A0SemanticPackage {
        schema: PACKAGE_SCHEMA.to_owned(),
        version: "3".to_owned(),
        source_path: "crates/axeyum-machine/src/a0.rs".to_owned(),
        source_sha256: sha256_hex(A0_SOURCE),
        word_widths: (8..=64).step_by(8).collect(),
        instruction_bytes: 4,
        byte_order: "little-endian".to_owned(),
        capabilities: [
            "words",
            "finite-memory",
            "state",
            "observations",
            "decode",
            "dynamic-effects",
            "step",
            "bounded-trace",
            "returned-prefix",
        ]
        .into_iter()
        .map(str::to_owned)
        .collect(),
    }
}

/// Writes canonical, newline-terminated pretty JSON.
///
/// # Errors
///
/// Returns an I/O or JSON error if serialization or writing fails.
pub fn write_json<T: Serialize>(path: &Path, value: &T) -> Result<(), EvidenceError> {
    let mut bytes = serde_json::to_vec_pretty(value)?;
    bytes.push(b'\n');
    fs::write(path, bytes)?;
    Ok(())
}

/// Loads and verifies an A0 semantic package against the compiled source.
///
/// # Errors
///
/// Returns a categorized error for malformed JSON, I/O failure, or any field
/// that differs from the compiled package.
pub fn load_semantic_package(path: &Path) -> Result<A0SemanticPackage, EvidenceError> {
    let bytes = fs::read(path)?;
    let package: A0SemanticPackage = serde_json::from_slice(&bytes)?;
    let current = semantic_package();
    if package != current {
        return Err(EvidenceError::SemanticPackageMismatch(
            "package fields or semantic source digest differ from this checker".to_owned(),
        ));
    }
    Ok(package)
}

/// Produces the exhaustive 8- and 16-bit byte split/join report.
///
/// # Errors
///
/// Returns an error if the supplied semantic package is not the compiled one.
pub fn word_roundtrip_report(package_path: &Path) -> Result<WordRoundtripReport, EvidenceError> {
    load_semantic_package(package_path)?;
    let package_bytes = fs::read(package_path)?;
    Ok(compute_word_roundtrip(
        sha256_hex(&package_bytes),
        ByteOrderControl::Declared,
    ))
}

/// Recomputes and checks a word-roundtrip report.
///
/// # Errors
///
/// Returns `semantic-mismatch` when the report differs from recomputation.
pub fn check_word_roundtrip(
    package_path: &Path,
    report_path: &Path,
) -> Result<WordRoundtripReport, EvidenceError> {
    check_word_roundtrip_with_control(package_path, report_path, ByteOrderControl::Declared)
}

/// Runs the required reversed-byte-order mutation against a report.
///
/// A sound report must be rejected, because the mutation changes 16-bit byte
/// reconstruction. This function returning `Ok` means the control failed to
/// fire and must be treated as a gate failure.
///
/// # Errors
///
/// Returns `semantic-mismatch` when the load-bearing control fires as expected.
pub fn check_word_roundtrip_reversed_control(
    package_path: &Path,
    report_path: &Path,
) -> Result<WordRoundtripReport, EvidenceError> {
    check_word_roundtrip_with_control(package_path, report_path, ByteOrderControl::Reversed)
}

/// Produces the canonical narrow-versus-broad observation report.
///
/// # Errors
///
/// Returns an error if the supplied semantic package is not the compiled one.
pub fn observation_separation_report(
    package_path: &Path,
) -> Result<ObservationSeparationReport, EvidenceError> {
    load_semantic_package(package_path)?;
    let package_bytes = fs::read(package_path)?;
    Ok(compute_observation_separation(
        sha256_hex(&package_bytes),
        ObservationControl::Declared,
    ))
}

/// Recomputes and checks the observation-separation report.
///
/// # Errors
///
/// Returns `semantic-mismatch` when the report differs from recomputation.
pub fn check_observation_separation(
    package_path: &Path,
    report_path: &Path,
) -> Result<ObservationSeparationReport, EvidenceError> {
    check_observation_separation_with_control(
        package_path,
        report_path,
        ObservationControl::Declared,
    )
}

/// Omits the requested separating register and requires report rejection.
///
/// # Errors
///
/// Returns `semantic-mismatch` when the load-bearing control fires.
pub fn check_observation_omission_control(
    package_path: &Path,
    report_path: &Path,
) -> Result<ObservationSeparationReport, EvidenceError> {
    check_observation_separation_with_control(
        package_path,
        report_path,
        ObservationControl::OmitSeparatingRegister,
    )
}

/// Produces the exhaustive width-8 A0 addition-step report.
///
/// # Errors
///
/// Returns an error if the supplied semantic package is not the compiled one.
pub fn add_step_report(package_path: &Path) -> Result<AddStepReport, EvidenceError> {
    load_semantic_package(package_path)?;
    let package_bytes = fs::read(package_path)?;
    Ok(compute_add_step(
        sha256_hex(&package_bytes),
        AddControl::Declared,
    ))
}

/// Recomputes and checks the exhaustive addition-step report.
///
/// # Errors
///
/// Returns `semantic-mismatch` when the report differs from recomputation.
pub fn check_add_step(
    package_path: &Path,
    report_path: &Path,
) -> Result<AddStepReport, EvidenceError> {
    check_add_step_with_control(package_path, report_path, AddControl::Declared)
}

/// Reads the wrong destination register and requires report rejection.
///
/// # Errors
///
/// Returns `semantic-mismatch` when the load-bearing control fires.
pub fn check_add_wrong_destination_control(
    package_path: &Path,
    report_path: &Path,
) -> Result<AddStepReport, EvidenceError> {
    check_add_step_with_control(package_path, report_path, AddControl::WrongDestination)
}

/// Produces the concrete 16-bit store/load and boundary-trap report.
///
/// # Errors
///
/// Returns an error if the supplied semantic package is not the compiled one.
pub fn memory_trace_report(package_path: &Path) -> Result<MemoryTraceReport, EvidenceError> {
    load_semantic_package(package_path)?;
    let package_bytes = fs::read(package_path)?;
    Ok(compute_memory_trace(
        sha256_hex(&package_bytes),
        MemoryControl::Declared,
    ))
}

/// Recomputes and checks the memory trace.
///
/// # Errors
///
/// Returns `semantic-mismatch` when the report differs from recomputation.
pub fn check_memory_trace(
    package_path: &Path,
    report_path: &Path,
) -> Result<MemoryTraceReport, EvidenceError> {
    check_memory_trace_with_control(package_path, report_path, MemoryControl::Declared)
}

/// Reverses the observed stored bytes and requires report rejection.
///
/// # Errors
///
/// Returns `semantic-mismatch` when the load-bearing control fires.
pub fn check_memory_byte_order_control(
    package_path: &Path,
    report_path: &Path,
) -> Result<MemoryTraceReport, EvidenceError> {
    check_memory_trace_with_control(package_path, report_path, MemoryControl::ReverseStoredBytes)
}

/// Produces the taken and untaken A0 branch traces.
///
/// # Errors
///
/// Returns an error if the supplied semantic package is not the compiled one.
pub fn branch_trace_report(package_path: &Path) -> Result<BranchTraceReport, EvidenceError> {
    load_semantic_package(package_path)?;
    let package_bytes = fs::read(package_path)?;
    Ok(compute_branch_trace(
        sha256_hex(&package_bytes),
        BranchControl::Declared,
    ))
}

/// Recomputes and checks both branch traces.
///
/// # Errors
///
/// Returns `semantic-mismatch` when the report differs from recomputation.
pub fn check_branch_trace(
    package_path: &Path,
    report_path: &Path,
) -> Result<BranchTraceReport, EvidenceError> {
    check_branch_trace_with_control(package_path, report_path, BranchControl::Declared)
}

/// Uses the current PC instead of sequential PC as the taken target base.
///
/// # Errors
///
/// Returns `semantic-mismatch` when the load-bearing control fires.
pub fn check_branch_target_control(
    package_path: &Path,
    report_path: &Path,
) -> Result<BranchTraceReport, EvidenceError> {
    check_branch_trace_with_control(package_path, report_path, BranchControl::WrongTargetBase)
}

/// Produces concrete coverage of the A0 runner classifications and resumption.
///
/// # Errors
///
/// Returns an error if the supplied semantic package is not the compiled one.
pub fn run_classification_report(
    package_path: &Path,
) -> Result<RunClassificationReport, EvidenceError> {
    load_semantic_package(package_path)?;
    let package_bytes = fs::read(package_path)?;
    Ok(compute_run_classification(
        sha256_hex(&package_bytes),
        RunControl::Declared,
    ))
}

/// Recomputes and checks every runner classification and the resumption law.
///
/// # Errors
///
/// Returns `semantic-mismatch` when the report differs from recomputation.
pub fn check_run_classification(
    package_path: &Path,
    report_path: &Path,
) -> Result<RunClassificationReport, EvidenceError> {
    check_run_classification_with_control(package_path, report_path, RunControl::Declared)
}

/// Mislabels a running returned prefix as halted and requires rejection.
///
/// # Errors
///
/// Returns `semantic-mismatch` when the load-bearing control fires.
pub fn check_run_false_halt_control(
    package_path: &Path,
    report_path: &Path,
) -> Result<RunClassificationReport, EvidenceError> {
    check_run_classification_with_control(package_path, report_path, RunControl::FalseHalt)
}

#[derive(Clone, Copy)]
enum ByteOrderControl {
    Declared,
    Reversed,
}

#[derive(Clone, Copy)]
enum ObservationControl {
    Declared,
    OmitSeparatingRegister,
}

#[derive(Clone, Copy)]
enum AddControl {
    Declared,
    WrongDestination,
}

#[derive(Clone, Copy)]
enum MemoryControl {
    Declared,
    ReverseStoredBytes,
}

#[derive(Clone, Copy)]
enum BranchControl {
    Declared,
    WrongTargetBase,
}

#[derive(Clone, Copy)]
enum RunControl {
    Declared,
    FalseHalt,
}

fn check_word_roundtrip_with_control(
    package_path: &Path,
    report_path: &Path,
    control: ByteOrderControl,
) -> Result<WordRoundtripReport, EvidenceError> {
    load_semantic_package(package_path)?;
    let package_bytes = fs::read(package_path)?;
    let claimed: WordRoundtripReport = serde_json::from_slice(&fs::read(report_path)?)?;
    let recomputed = compute_word_roundtrip(sha256_hex(&package_bytes), control);
    if claimed != recomputed {
        return Err(EvidenceError::SemanticMismatch(format!(
            "claimed report does not equal recomputation (claimed result {}, recomputed {})",
            claimed.result_sha256, recomputed.result_sha256
        )));
    }
    Ok(claimed)
}

fn compute_word_roundtrip(
    semantic_package_sha256: String,
    control: ByteOrderControl,
) -> WordRoundtripReport {
    let mut result = Sha256::new();
    let mut values_checked = 0_u64;
    let mut passed = true;
    for width in [8_u8, 16] {
        let limit = 1_u64 << width;
        for value in 0..limit {
            let word = Word::new(width, value).expect("enumerated width is supported");
            let mut bytes = word.little_endian_bytes();
            if matches!(control, ByteOrderControl::Reversed) {
                bytes.reverse();
            }
            let reconstructed =
                Word::from_little_endian(&bytes).expect("one- or two-byte word is supported");
            passed &= reconstructed == word;
            result.update([width]);
            result.update(value.to_le_bytes());
            result.update([u8::try_from(bytes.len()).expect("word has at most eight bytes")]);
            result.update(&bytes);
            result.update(reconstructed.unsigned().to_le_bytes());
            values_checked += 1;
        }
    }
    WordRoundtripReport {
        schema: ROUNDTRIP_SCHEMA.to_owned(),
        semantic_package_sha256,
        exhaustive_widths: vec![8, 16],
        values_checked,
        passed,
        result_sha256: hex_digest(result.finalize()),
    }
}

fn check_observation_separation_with_control(
    package_path: &Path,
    report_path: &Path,
    control: ObservationControl,
) -> Result<ObservationSeparationReport, EvidenceError> {
    load_semantic_package(package_path)?;
    let package_bytes = fs::read(package_path)?;
    let claimed: ObservationSeparationReport = serde_json::from_slice(&fs::read(report_path)?)?;
    let recomputed = compute_observation_separation(sha256_hex(&package_bytes), control);
    if claimed != recomputed {
        return Err(EvidenceError::SemanticMismatch(format!(
            "claimed observation report does not equal recomputation (claimed broad_equal={}, recomputed broad_equal={})",
            claimed.broad_equal, recomputed.broad_equal
        )));
    }
    Ok(claimed)
}

fn compute_observation_separation(
    semantic_package_sha256: String,
    control: ObservationControl,
) -> ObservationSeparationReport {
    let mut left = State::new(8, Memory::from_bytes(vec![0xaa, 0xbb, 0xcc, 0xdd]), word(0))
        .expect("fixed observation state is valid");
    left.registers[0] = word(7);
    left.registers[3] = word(19);
    let mut right = left.clone();
    right.registers[3] = word(20);

    let narrow_registers = vec![0];
    let broad_registers = if matches!(control, ObservationControl::Declared) {
        vec![0, 3]
    } else {
        vec![0]
    };
    let narrow = Observation::new(narrow_registers.clone(), vec![])
        .expect("fixed narrow observation is valid")
        .with_outcome();
    let broad = Observation::new(
        broad_registers.clone(),
        vec![MemorySpan { start: 1, len: 2 }],
    )
    .expect("fixed broad observation is valid")
    .with_program_counter()
    .with_conditions()
    .with_outcome();
    let left_narrow = narrow
        .apply(&left)
        .expect("fixed narrow observation applies");
    let right_narrow = narrow
        .apply(&right)
        .expect("fixed narrow observation applies");
    let left_broad = broad.apply(&left).expect("fixed broad observation applies");
    let right_broad = broad
        .apply(&right)
        .expect("fixed broad observation applies");
    let separating_register = broad_registers
        .iter()
        .copied()
        .find(|index| left.registers[usize::from(*index)] != right.registers[usize::from(*index)]);
    let left_value = separating_register.map(|index| left.registers[usize::from(index)].unsigned());
    let right_value =
        separating_register.map(|index| right.registers[usize::from(index)].unsigned());

    ObservationSeparationReport {
        schema: OBSERVATION_SCHEMA.to_owned(),
        semantic_package_sha256,
        witness_states_sha256: observation_witness_digest(&left, &right),
        narrow_registers,
        broad_registers,
        narrow_equal: left_narrow == right_narrow,
        broad_equal: left_broad == right_broad,
        separating_register,
        left_value,
        right_value,
    }
}

fn check_add_step_with_control(
    package_path: &Path,
    report_path: &Path,
    control: AddControl,
) -> Result<AddStepReport, EvidenceError> {
    load_semantic_package(package_path)?;
    let package_bytes = fs::read(package_path)?;
    let claimed: AddStepReport = serde_json::from_slice(&fs::read(report_path)?)?;
    let recomputed = compute_add_step(sha256_hex(&package_bytes), control);
    if claimed != recomputed {
        return Err(EvidenceError::SemanticMismatch(format!(
            "claimed add report does not equal recomputation (claimed destination r{}, recomputed r{})",
            claimed.destination, recomputed.destination
        )));
    }
    Ok(claimed)
}

fn compute_add_step(semantic_package_sha256: String, control: AddControl) -> AddStepReport {
    let program =
        Program::new(8, word(0), vec![0x10, 0x02, 0x01, 0]).expect("fixed add program is valid");
    let destination = if matches!(control, AddControl::Declared) {
        2
    } else {
        3
    };
    let mut result_digest = Sha256::new();
    let mut passed = true;
    let mut cases_checked = 0_u64;
    for lhs in 0_u16..=255 {
        for rhs in 0_u16..=255 {
            let mut before =
                State::new(8, Memory::zeroed(0), word(0)).expect("fixed add state is valid");
            before.registers[0] = word(u64::from(lhs));
            before.registers[1] = word(u64::from(rhs));
            let after = step(&program, &before);
            let actual = after.registers[usize::from(destination)].unsigned();
            let expected = lhs.wrapping_add(rhs) & 0xff;
            let overflow = (lhs & 0x80) == (rhs & 0x80) && (expected & 0x80) != (lhs & 0x80);
            passed &= actual == u64::from(expected)
                && after.conditions.zero == (expected == 0)
                && after.conditions.negative == (expected & 0x80 != 0)
                && after.conditions.carry == (lhs + rhs >= 256)
                && after.conditions.overflow == overflow
                && after.pc == word(4)
                && after.registers[0] == before.registers[0]
                && after.registers[1] == before.registers[1]
                && after.outcome == Outcome::Running;
            result_digest.update(lhs.to_le_bytes());
            result_digest.update(rhs.to_le_bytes());
            result_digest.update(actual.to_le_bytes());
            result_digest.update([
                u8::from(after.conditions.zero),
                u8::from(after.conditions.negative),
                u8::from(after.conditions.carry),
                u8::from(after.conditions.overflow),
            ]);
            result_digest.update(after.pc.unsigned().to_le_bytes());
            cases_checked += 1;
        }
    }
    AddStepReport {
        schema: ADD_SCHEMA.to_owned(),
        semantic_package_sha256,
        width: 8,
        destination,
        cases_checked,
        passed,
        result_sha256: hex_digest(result_digest.finalize()),
    }
}

fn check_memory_trace_with_control(
    package_path: &Path,
    report_path: &Path,
    control: MemoryControl,
) -> Result<MemoryTraceReport, EvidenceError> {
    load_semantic_package(package_path)?;
    let package_bytes = fs::read(package_path)?;
    let claimed: MemoryTraceReport = serde_json::from_slice(&fs::read(report_path)?)?;
    let recomputed = compute_memory_trace(sha256_hex(&package_bytes), control);
    if claimed != recomputed {
        return Err(EvidenceError::SemanticMismatch(format!(
            "claimed memory report does not equal recomputation (claimed bytes {:?}, recomputed {:?})",
            claimed.stored_bytes, recomputed.stored_bytes
        )));
    }
    Ok(claimed)
}

fn compute_memory_trace(
    semantic_package_sha256: String,
    control: MemoryControl,
) -> MemoryTraceReport {
    let program = Program::new(16, word16(0), vec![0x03, 0x08, 0x02, 1, 0x02, 0x0b, 0, 1])
        .expect("fixed memory program is valid");
    let mut initial =
        State::new(16, Memory::zeroed(4), word16(0)).expect("fixed memory state is valid");
    initial.registers[1] = word16(0);
    initial.registers[2] = word16(0xabcd);
    let stored = step(&program, &initial);
    let loaded = step(&program, &stored);
    let mut stored_bytes = vec![
        stored.memory.byte(1).expect("stored byte is in range"),
        stored.memory.byte(2).expect("stored byte is in range"),
    ];
    if matches!(control, MemoryControl::ReverseStoredBytes) {
        stored_bytes.reverse();
    }

    let trap_program = Program::new(16, word16(0), vec![0x03, 0x08, 0x02, 0])
        .expect("fixed trap program is valid");
    let mut trap_initial =
        State::new(16, Memory::zeroed(4), word16(0)).expect("fixed trap state is valid");
    trap_initial.registers[1] = word16(4);
    trap_initial.registers[2] = word16(0xabcd);
    let trapped = step(&trap_program, &trap_initial);

    MemoryTraceReport {
        schema: MEMORY_SCHEMA.to_owned(),
        semantic_package_sha256,
        stored_word: 0xabcd,
        stored_bytes,
        loaded_word: loaded.registers[3].unsigned(),
        boundary_trapped: matches!(trapped.outcome, Outcome::Trapped(Trap::DataRange { .. })),
        no_partial_write: trapped.memory == trap_initial.memory,
        successful_pcs: vec![
            initial.pc.unsigned(),
            stored.pc.unsigned(),
            loaded.pc.unsigned(),
        ],
    }
}

fn check_branch_trace_with_control(
    package_path: &Path,
    report_path: &Path,
    control: BranchControl,
) -> Result<BranchTraceReport, EvidenceError> {
    load_semantic_package(package_path)?;
    let package_bytes = fs::read(package_path)?;
    let claimed: BranchTraceReport = serde_json::from_slice(&fs::read(report_path)?)?;
    let recomputed = compute_branch_trace(sha256_hex(&package_bytes), control);
    if claimed != recomputed {
        return Err(EvidenceError::SemanticMismatch(format!(
            "claimed branch report does not equal recomputation (claimed taken PCs {:?}, recomputed {:?})",
            claimed.taken_pcs, recomputed.taken_pcs
        )));
    }
    Ok(claimed)
}

fn compute_branch_trace(
    semantic_package_sha256: String,
    control: BranchControl,
) -> BranchTraceReport {
    let program = Program::new(
        8,
        word(0),
        vec![0x30, 0, 0, 1, 0xff, 0, 0, 0, 0xff, 0, 0, 0],
    )
    .expect("fixed branch program is valid");
    let mut taken_initial =
        State::new(8, Memory::zeroed(0), word(0)).expect("fixed branch state is valid");
    taken_initial.conditions.zero = true;
    let mut untaken_initial = taken_initial.clone();
    untaken_initial.conditions.zero = false;
    let taken = run(&program, taken_initial, 2);
    let untaken = run(&program, untaken_initial, 2);
    let mut taken_pcs: Vec<u64> = taken
        .states
        .iter()
        .map(|state| state.pc.unsigned())
        .collect();
    if matches!(control, BranchControl::WrongTargetBase) {
        taken_pcs[1] = 4;
    }
    BranchTraceReport {
        schema: BRANCH_SCHEMA.to_owned(),
        semantic_package_sha256,
        taken_pcs,
        untaken_pcs: untaken
            .states
            .iter()
            .map(|state| state.pc.unsigned())
            .collect(),
        taken_stop: stop_label(taken.stop).to_owned(),
        untaken_stop: stop_label(untaken.stop).to_owned(),
    }
}

fn check_run_classification_with_control(
    package_path: &Path,
    report_path: &Path,
    control: RunControl,
) -> Result<RunClassificationReport, EvidenceError> {
    load_semantic_package(package_path)?;
    let package_bytes = fs::read(package_path)?;
    let claimed: RunClassificationReport = serde_json::from_slice(&fs::read(report_path)?)?;
    let recomputed = compute_run_classification(sha256_hex(&package_bytes), control);
    if claimed != recomputed {
        return Err(EvidenceError::SemanticMismatch(format!(
            "claimed runner report does not equal recomputation (claimed prefix stop {}, recomputed {})",
            claimed.prefix_stop, recomputed.prefix_stop
        )));
    }
    Ok(claimed)
}

fn compute_run_classification(
    semantic_package_sha256: String,
    control: RunControl,
) -> RunClassificationReport {
    let halt_program =
        Program::new(8, word(0), vec![0xff, 0, 0, 0]).expect("fixed halt program is valid");
    let trap_program =
        Program::new(8, word(0), vec![0x99, 0, 0, 0]).expect("fixed trap program is valid");
    let loop_program =
        Program::new(8, word(0), vec![0x31, 0, 0, 0xff]).expect("fixed loop program is valid");
    let initial = State::new(8, Memory::zeroed(0), word(0)).expect("fixed state is valid");
    let halted = run(&halt_program, initial.clone(), 4);
    let trapped = run(&trap_program, initial.clone(), 4);
    let exhausted = run(&loop_program, initial.clone(), 3);
    let zero = run(&loop_program, initial.clone(), 0);
    let first = run_prefix(&loop_program, initial.clone(), 2);
    let second = run_prefix(
        &loop_program,
        first
            .states
            .last()
            .expect("prefix has a final state")
            .clone(),
        3,
    );
    let whole = run_prefix(&loop_program, initial, 5);
    let mut resumed = first.states;
    resumed.extend(second.states.into_iter().skip(1));
    let prefix_stop = if matches!(control, RunControl::FalseHalt) {
        "halted".to_owned()
    } else {
        stop_label(whole.stop).to_owned()
    };
    RunClassificationReport {
        schema: RUN_SCHEMA.to_owned(),
        semantic_package_sha256,
        halted_stop: stop_label(halted.stop).to_owned(),
        trapped_stop: stop_label(trapped.stop).to_owned(),
        exhausted_stop: stop_label(exhausted.stop).to_owned(),
        prefix_stop,
        zero_bound_states: zero.states.len(),
        resumed_equals_whole: resumed == whole.states,
        resumed_pcs: resumed.iter().map(|state| state.pc.unsigned()).collect(),
    }
}

const fn stop_label(stop: StopReason) -> &'static str {
    match stop {
        StopReason::Halted => "halted",
        StopReason::Trapped => "trapped",
        StopReason::BoundExhausted => "bound-exhausted",
        StopReason::PrefixReturned => "prefix-returned",
    }
}

fn observation_witness_digest(left: &State, right: &State) -> String {
    let mut digest = Sha256::new();
    for state in [left, right] {
        digest.update([state.width()]);
        for register in state.registers {
            digest.update(register.unsigned().to_le_bytes());
        }
        digest.update(
            u64::try_from(state.memory.len())
                .expect("memory length fits u64")
                .to_le_bytes(),
        );
        for address in 0..state.memory.len() {
            digest.update([state.memory.byte(address).expect("address is in range")]);
        }
        digest.update(state.pc.unsigned().to_le_bytes());
        digest.update([
            u8::from(state.conditions.zero),
            u8::from(state.conditions.negative),
            u8::from(state.conditions.carry),
            u8::from(state.conditions.overflow),
        ]);
        digest.update([0]);
    }
    hex_digest(digest.finalize())
}

fn word(value: u64) -> Word {
    Word::new(8, value).expect("fixed evidence word width is valid")
}

fn word16(value: u64) -> Word {
    Word::new(16, value).expect("fixed evidence word width is valid")
}

fn sha256_hex(bytes: &[u8]) -> String {
    hex_digest(Sha256::digest(bytes))
}

fn hex_digest(bytes: impl AsRef<[u8]>) -> String {
    let bytes = bytes.as_ref();
    let mut output = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        use core::fmt::Write as _;
        write!(&mut output, "{byte:02x}").expect("writing to String cannot fail");
    }
    output
}
