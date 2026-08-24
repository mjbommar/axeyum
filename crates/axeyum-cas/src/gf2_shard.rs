//! Canonical manifests and independent admission for sparse-search shards.

use core::fmt::{self, Write as _};
use std::fs;
use std::path::Path;

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

use crate::gf2::Gf2Limits;
use crate::gf2_artifact::{ArtifactLimits, from_canonical_json};

/// Shard manifest format tag.
pub const SHARD_FORMAT: &str = "axeyum-gf2-lemire-search-shard";
/// Shard manifest version.
pub const SHARD_VERSION: u32 = 1;
/// Canonical manifest file name inside every shard directory.
pub const MANIFEST_FILE: &str = "manifest.json";

/// Search disposition for exactly one degree.
#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum ShardStatus {
    /// A checked artifact was emitted.
    Found,
    /// Every configured sparse candidate was reducible.
    Exhausted,
    /// The candidate ceiling stopped enumeration before exhaustion.
    CandidateLimit,
}

/// One degree's deterministic search receipt.
#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ShardRow {
    /// Degree searched.
    pub degree: usize,
    /// Typed search disposition.
    pub status: ShardStatus,
    /// Candidates actually tested.
    pub candidates_tested: u64,
    /// Tail-term count for a found polynomial.
    pub tail_terms: Option<usize>,
    /// Canonical artifact basename for a found polynomial.
    pub artifact: Option<String>,
    /// SHA-256 of the exact canonical artifact bytes.
    pub artifact_sha256: Option<String>,
}

/// Content-bound deterministic search manifest.
#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ShardManifest {
    /// Fixed format identity.
    pub format: String,
    /// Fixed format version.
    pub version: u32,
    /// Exact untrusted producer/source identity.
    pub producer: String,
    /// Inclusive first degree.
    pub start_degree: usize,
    /// Inclusive last degree.
    pub end_degree: usize,
    /// Sparse tail-term ceiling.
    pub max_tail_terms: usize,
    /// Per-degree candidate ceiling.
    pub max_candidates_per_degree: u64,
    /// Per-candidate packed arithmetic limits.
    pub arithmetic_limits: ManifestArithmeticLimits,
    /// Exactly one ordered row for every degree in the inclusive range.
    pub rows: Vec<ShardRow>,
}

/// Serialized projection of [`Gf2Limits`].
#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ManifestArithmeticLimits {
    /// Maximum candidate degree.
    pub max_input_degree: usize,
    /// Maximum intermediate degree.
    pub max_intermediate_degree: usize,
    /// Maximum Frobenius steps.
    pub max_frobenius_steps: usize,
    /// Maximum word operations per candidate.
    pub max_word_ops: u64,
}

impl From<Gf2Limits> for ManifestArithmeticLimits {
    fn from(limits: Gf2Limits) -> Self {
        Self {
            max_input_degree: limits.max_input_degree,
            max_intermediate_degree: limits.max_intermediate_degree,
            max_frobenius_steps: limits.max_frobenius_steps,
            max_word_ops: limits.max_word_ops,
        }
    }
}

/// Independently derived shard admission summary.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ShardCheckSummary {
    /// Total degree rows.
    pub rows: usize,
    /// Rows with admitted artifacts.
    pub found: usize,
    /// Completely exhausted sparse layers.
    pub exhausted: usize,
    /// Rows stopped by their candidate ceiling.
    pub candidate_limit: usize,
}

/// Fail-closed shard format, I/O, hash, or artifact error.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ShardError {
    /// Filesystem read failure.
    Io(String),
    /// JSON syntax or type failure.
    Json(String),
    /// Canonical/structural manifest invariant failed.
    Format(&'static str),
    /// A child witness artifact failed admission.
    Artifact {
        /// Degree whose child artifact failed.
        degree: usize,
        /// Child hash/parser/checker error.
        error: String,
    },
}

impl fmt::Display for ShardError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Io(message) => write!(formatter, "shard I/O failure: {message}"),
            Self::Json(message) => write!(formatter, "invalid shard JSON: {message}"),
            Self::Format(message) => write!(formatter, "invalid shard format: {message}"),
            Self::Artifact { degree, error } => {
                write!(formatter, "degree-{degree} artifact failed: {error}")
            }
        }
    }
}

impl std::error::Error for ShardError {}

/// Render a structurally valid manifest as canonical JSON.
///
/// # Errors
///
/// Returns a format or serialization error.
pub fn to_canonical_manifest_json(manifest: &ShardManifest) -> Result<String, ShardError> {
    validate_manifest(manifest)?;
    let mut output = serde_json::to_string_pretty(manifest)
        .map_err(|error| ShardError::Json(error.to_string()))?;
    output.push('\n');
    Ok(output)
}

/// Parse canonical manifest bytes and validate the complete degree population.
///
/// # Errors
///
/// Returns a JSON or format error, including for noncanonical bytes.
pub fn from_canonical_manifest_json(input: &str) -> Result<ShardManifest, ShardError> {
    let manifest: ShardManifest =
        serde_json::from_str(input).map_err(|error| ShardError::Json(error.to_string()))?;
    validate_manifest(&manifest)?;
    if to_canonical_manifest_json(&manifest)? != input {
        return Err(ShardError::Format("manifest JSON is not canonical"));
    }
    Ok(manifest)
}

/// Read a shard, bind every artifact hash, and run both artifact checkers.
///
/// # Errors
///
/// Returns a typed I/O, manifest, hash, or child-certificate error.
pub fn check_shard_directory(
    directory: &Path,
    artifact_limits: ArtifactLimits,
) -> Result<ShardCheckSummary, ShardError> {
    let manifest_path = directory.join(MANIFEST_FILE);
    let manifest_bytes = fs::read_to_string(&manifest_path)
        .map_err(|error| ShardError::Io(format!("{}: {error}", manifest_path.display())))?;
    if manifest_bytes.len() > 4 * 1024 * 1024 {
        return Err(ShardError::Format("manifest exceeds 4 MiB"));
    }
    let manifest = from_canonical_manifest_json(&manifest_bytes)?;
    let mut summary = ShardCheckSummary {
        rows: manifest.rows.len(),
        found: 0,
        exhausted: 0,
        candidate_limit: 0,
    };
    for row in &manifest.rows {
        match row.status {
            ShardStatus::Found => {
                let expected_name = format!("degree-{}.json", row.degree);
                let artifact_name = row
                    .artifact
                    .as_deref()
                    .ok_or(ShardError::Format("found row has no artifact"))?;
                if artifact_name != expected_name {
                    return Err(ShardError::Format("artifact basename is not canonical"));
                }
                let expected_hash = row
                    .artifact_sha256
                    .as_deref()
                    .ok_or(ShardError::Format("found row has no artifact hash"))?;
                if expected_hash.len() != 64
                    || !expected_hash
                        .bytes()
                        .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
                {
                    return Err(ShardError::Format("artifact hash is not lowercase SHA-256"));
                }
                let artifact_path = directory.join(artifact_name);
                let bytes = fs::read_to_string(&artifact_path).map_err(|error| {
                    ShardError::Io(format!("{}: {error}", artifact_path.display()))
                })?;
                if sha256_hex(bytes.as_bytes()) != expected_hash {
                    return Err(ShardError::Artifact {
                        degree: row.degree,
                        error: "SHA-256 differs from manifest".to_owned(),
                    });
                }
                let artifact = from_canonical_json(&bytes, artifact_limits).map_err(|error| {
                    ShardError::Artifact {
                        degree: row.degree,
                        error: error.to_string(),
                    }
                })?;
                if artifact.certificate.polynomial.degree() != Some(row.degree) {
                    return Err(ShardError::Artifact {
                        degree: row.degree,
                        error: "artifact degree differs from row".to_owned(),
                    });
                }
                if artifact.producer != manifest.producer {
                    return Err(ShardError::Artifact {
                        degree: row.degree,
                        error: "artifact producer differs from manifest".to_owned(),
                    });
                }
                summary.found += 1;
            }
            ShardStatus::Exhausted => summary.exhausted += 1,
            ShardStatus::CandidateLimit => summary.candidate_limit += 1,
        }
    }
    Ok(summary)
}

/// SHA-256 rendered as lowercase hexadecimal.
#[must_use]
pub fn sha256_hex(bytes: &[u8]) -> String {
    let digest = Sha256::digest(bytes);
    let mut output = String::with_capacity(64);
    for byte in digest {
        let _ = write!(output, "{byte:02x}");
    }
    output
}

fn validate_manifest(manifest: &ShardManifest) -> Result<(), ShardError> {
    if manifest.format != SHARD_FORMAT {
        return Err(ShardError::Format("unknown manifest format"));
    }
    if manifest.version != SHARD_VERSION {
        return Err(ShardError::Format("unsupported manifest version"));
    }
    if manifest.producer.is_empty()
        || manifest.producer.len() > 256
        || manifest.producer.chars().any(char::is_control)
    {
        return Err(ShardError::Format("invalid producer identity"));
    }
    if manifest.start_degree == 0 || manifest.start_degree > manifest.end_degree {
        return Err(ShardError::Format("invalid inclusive degree range"));
    }
    if manifest.max_tail_terms == 0 || !manifest.max_tail_terms.is_multiple_of(2) {
        return Err(ShardError::Format("invalid tail-term policy"));
    }
    let expected_rows = manifest.end_degree - manifest.start_degree + 1;
    if manifest.rows.len() != expected_rows {
        return Err(ShardError::Format(
            "row population differs from degree range",
        ));
    }
    for (offset, row) in manifest.rows.iter().enumerate() {
        if row.degree != manifest.start_degree + offset {
            return Err(ShardError::Format("rows are not complete and ordered"));
        }
        match row.status {
            ShardStatus::Found => {
                if row.tail_terms.is_none()
                    || row.artifact.is_none()
                    || row.artifact_sha256.is_none()
                {
                    return Err(ShardError::Format("found row lacks evidence fields"));
                }
            }
            ShardStatus::Exhausted | ShardStatus::CandidateLimit => {
                if row.tail_terms.is_some()
                    || row.artifact.is_some()
                    || row.artifact_sha256.is_some()
                {
                    return Err(ShardError::Format("non-found row carries evidence fields"));
                }
            }
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn control() -> ShardManifest {
        ShardManifest {
            format: SHARD_FORMAT.to_owned(),
            version: SHARD_VERSION,
            producer: "test-producer".to_owned(),
            start_degree: 2,
            end_degree: 3,
            max_tail_terms: 4,
            max_candidates_per_degree: 100,
            arithmetic_limits: Gf2Limits::default().into(),
            rows: vec![
                ShardRow {
                    degree: 2,
                    status: ShardStatus::Exhausted,
                    candidates_tested: 1,
                    tail_terms: None,
                    artifact: None,
                    artifact_sha256: None,
                },
                ShardRow {
                    degree: 3,
                    status: ShardStatus::CandidateLimit,
                    candidates_tested: 100,
                    tail_terms: None,
                    artifact: None,
                    artifact_sha256: None,
                },
            ],
        }
    }

    #[test]
    fn canonical_manifest_round_trip() {
        let manifest = control();
        let json = to_canonical_manifest_json(&manifest).unwrap();
        assert_eq!(from_canonical_manifest_json(&json).unwrap(), manifest);
        assert!(matches!(
            from_canonical_manifest_json(&json.replace("  \"format\"", " \"format\"")),
            Err(ShardError::Format("manifest JSON is not canonical"))
        ));
    }

    #[test]
    fn population_and_evidence_fields_fail_closed() {
        let mut missing = control();
        missing.rows.pop();
        assert!(matches!(
            to_canonical_manifest_json(&missing),
            Err(ShardError::Format(_))
        ));
        let mut false_credit = control();
        false_credit.rows[0].artifact = Some("degree-2.json".to_owned());
        assert!(matches!(
            to_canonical_manifest_json(&false_credit),
            Err(ShardError::Format(_))
        ));
    }

    #[test]
    fn sha256_is_stable() {
        assert_eq!(
            sha256_hex(b"abc"),
            "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
        );
    }
}
