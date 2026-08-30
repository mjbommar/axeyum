//! Content-bound evidence producers and replay checkers for machine semantics.
//!
//! This crate consumes `axeyum-machine`; it does not define another machine.
//! Reports bind the exact semantic source digest, declare their finite domain,
//! and are accepted only after the checker recomputes the result.

use std::{fs, path::Path};

use axeyum_machine::a0::Word;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

const A0_SOURCE: &[u8] = include_bytes!("../../axeyum-machine/src/a0.rs");
const PACKAGE_SCHEMA: &str = "axeyum.a0.semantic-package.v1";
const ROUNDTRIP_SCHEMA: &str = "axeyum.a0.word-roundtrip.v1";

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
        version: "1".to_owned(),
        source_path: "crates/axeyum-machine/src/a0.rs".to_owned(),
        source_sha256: sha256_hex(A0_SOURCE),
        word_widths: (8..=64).step_by(8).collect(),
        instruction_bytes: 4,
        byte_order: "little-endian".to_owned(),
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

#[derive(Clone, Copy)]
enum ByteOrderControl {
    Declared,
    Reversed,
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
