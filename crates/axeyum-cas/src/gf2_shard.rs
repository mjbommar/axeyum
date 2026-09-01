//! Canonical manifests and independent admission for sparse-search shards.

use core::fmt::{self, Write as _};
use std::fs;
use std::path::Path;

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

use crate::gf2::Gf2Limits;
use crate::gf2_artifact::{ArtifactLimits, from_canonical_json};
use crate::gf2_search::{SparseSearchLimits, SparseSearchOutcome, search_sparse_half_degree};

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

impl From<ManifestArithmeticLimits> for Gf2Limits {
    fn from(limits: ManifestArithmeticLimits) -> Self {
        Self {
            max_input_degree: limits.max_input_degree,
            max_intermediate_degree: limits.max_intermediate_degree,
            max_frobenius_steps: limits.max_frobenius_steps,
            max_word_ops: limits.max_word_ops,
        }
    }
}

/// Admission policy for a shard, including the negative-row re-derivation budget.
///
/// An [`ShardStatus::Exhausted`] row is a *negative theorem*: every sparse
/// candidate the policy admits at that degree is reducible.  Nothing in the
/// manifest witnesses it, and no field could -- the claim is about the absence
/// of a witness.  So this checker re-runs the producer's own deterministic
/// enumeration and requires the identical verdict *and* the identical candidate
/// count.  Per ADR-1400 that is a re-derivation rather than a recorded field,
/// and a forged exhaustion cannot survive it.
///
/// Re-derivation costs real work, so it is budgeted.  Exhausting the budget is a
/// typed [`ShardError::Exhaustion`] failure and **never** a silent acceptance:
/// a checker that cannot fail is worse than no checker.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ShardCheckPolicy {
    /// Per-artifact certificate checking limits.
    pub artifact_limits: ArtifactLimits,
    /// Total candidates this checker may retest across every negative row.
    ///
    /// Zero means "re-derive nothing", which turns every exhaustion claim into a
    /// typed failure rather than into an acceptance.
    pub max_rederived_candidates: u64,
}

impl ShardCheckPolicy {
    /// Default budget for re-deriving exhaustion claims.
    pub const DEFAULT_REDERIVED_CANDIDATES: u64 = 4_000_000;

    /// Policy with the default re-derivation budget and the supplied artifact limits.
    #[must_use]
    pub const fn with_artifact_limits(artifact_limits: ArtifactLimits) -> Self {
        Self {
            artifact_limits,
            max_rederived_candidates: Self::DEFAULT_REDERIVED_CANDIDATES,
        }
    }
}

impl Default for ShardCheckPolicy {
    fn default() -> Self {
        Self::with_artifact_limits(ArtifactLimits::default())
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
    /// Candidates this checker retested while re-deriving exhaustion claims.
    ///
    /// Zero with a nonzero [`ShardCheckSummary::exhausted`] is impossible: every
    /// admitted exhaustion row is re-derived, and re-derivation tests at least
    /// the candidates the row claims to have tested.
    pub rederived_candidates: u64,
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
    /// A negative (non-`Found`) row's claim failed independent re-derivation.
    Exhaustion {
        /// Degree whose negative claim failed.
        degree: usize,
        /// What the re-derivation found instead.
        error: String,
    },
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
            Self::Exhaustion { degree, error } => write!(
                formatter,
                "degree-{degree} negative claim failed re-derivation: {error}"
            ),
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

/// Read a shard, bind every artifact hash, run both artifact checkers, and
/// independently re-derive every negative row, under the default policy.
///
/// # Errors
///
/// Returns a typed I/O, manifest, hash, re-derivation, or child-certificate error.
pub fn check_shard_directory(
    directory: &Path,
    artifact_limits: ArtifactLimits,
) -> Result<ShardCheckSummary, ShardError> {
    check_shard_directory_with_policy(
        directory,
        ShardCheckPolicy::with_artifact_limits(artifact_limits),
    )
}

/// Read a shard, bind every artifact hash, run both artifact checkers, and
/// independently re-derive every negative row, under an explicit policy.
///
/// # Errors
///
/// Returns a typed I/O, manifest, hash, re-derivation, or child-certificate error.
pub fn check_shard_directory_with_policy(
    directory: &Path,
    policy: ShardCheckPolicy,
) -> Result<ShardCheckSummary, ShardError> {
    let artifact_limits = policy.artifact_limits;
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
        rederived_candidates: 0,
    };
    let mut remaining_budget = policy.max_rederived_candidates;
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
                check_found_row_shape(row, manifest.max_tail_terms, &artifact.certificate)?;
                summary.found += 1;
            }
            ShardStatus::Exhausted => {
                let tested = rederive_exhaustion(manifest_view(&manifest), row, remaining_budget)?;
                remaining_budget = remaining_budget.saturating_sub(tested);
                summary.rederived_candidates += tested;
                summary.exhausted += 1;
            }
            ShardStatus::CandidateLimit => {
                // A `CandidateLimit` row claims exactly the opposite of an
                // exhaustion: enumeration stopped AT the ceiling.  The producer
                // returns the ceiling verbatim, so that is re-derivable from the
                // manifest with no search at all -- and without this check a row
                // may claim a ceiling stop after testing nothing.
                if row.candidates_tested != manifest.max_candidates_per_degree {
                    return Err(ShardError::Exhaustion {
                        degree: row.degree,
                        error: format!(
                            "candidate-limit row tested {} of a {} ceiling",
                            row.candidates_tested, manifest.max_candidates_per_degree
                        ),
                    });
                }
                summary.candidate_limit += 1;
            }
        }
    }
    Ok(summary)
}

/// Search policy the manifest itself declares, as the producer would have used it.
fn manifest_view(manifest: &ShardManifest) -> SparseSearchLimits {
    SparseSearchLimits {
        max_tail_terms: manifest.max_tail_terms,
        max_candidates: manifest.max_candidates_per_degree,
        arithmetic: manifest.arithmetic_limits.into(),
    }
}

/// Re-derive one exhaustion claim by re-running the producer's own enumeration.
///
/// Returns the number of candidates retested, which is charged to the budget.
fn rederive_exhaustion(
    limits: SparseSearchLimits,
    row: &ShardRow,
    remaining_budget: u64,
) -> Result<u64, ShardError> {
    // The re-derivation runs under the SMALLER of the manifest's own ceiling and
    // what is left of this checker's budget.  Both stops are refusals, and the
    // message says which, but neither is ever an acceptance.
    //
    // There is deliberately no separate "the row claims more than the budget"
    // pre-check.  It looked like a guard and was not: every input it would have
    // rejected is already rejected here or by the candidate-count binding below,
    // so no test could kill it.  A guard nothing can kill is the defect this
    // module is being repaired for, arriving one level up.
    let stopped_by_budget = remaining_budget < limits.max_candidates;
    let budgeted = SparseSearchLimits {
        max_candidates: remaining_budget.min(limits.max_candidates),
        ..limits
    };
    match search_sparse_half_degree(row.degree, budgeted) {
        Ok(SparseSearchOutcome::Exhausted { candidates_tested }) => {
            if candidates_tested != row.candidates_tested {
                return Err(ShardError::Exhaustion {
                    degree: row.degree,
                    error: format!(
                        "re-derivation tested {candidates_tested} candidates, row claims {}",
                        row.candidates_tested
                    ),
                });
            }
            Ok(candidates_tested)
        }
        Ok(SparseSearchOutcome::Found {
            candidates_tested, ..
        }) => Err(ShardError::Exhaustion {
            degree: row.degree,
            error: format!(
                "re-derivation certified an irreducible candidate after {candidates_tested} tests"
            ),
        }),
        Ok(SparseSearchOutcome::CandidateLimit {
            candidates_tested, ..
        }) => Err(ShardError::Exhaustion {
            degree: row.degree,
            error: if stopped_by_budget {
                format!(
                    "re-derivation stopped at the checker's remaining budget of \
                     {remaining_budget} after {candidates_tested} tests, so the \
                     exhaustion is unchecked"
                )
            } else {
                format!(
                    "re-derivation reached the manifest's own {} candidate ceiling \
                     after {candidates_tested} tests, which is a candidate-limit \
                     row and not an exhaustion",
                    limits.max_candidates
                )
            },
        }),
        Err(error) => Err(ShardError::Exhaustion {
            degree: row.degree,
            error: format!("re-derivation declined: {error}"),
        }),
    }
}

/// Re-derive a found row's search-policy fields from the admitted polynomial.
///
/// `tail_terms` is recorded, so it can be forged; it is re-derivable from the
/// artifact, so it is not taken on trust.  The half-degree and sparse-layer
/// constraints are what make the shard's `Exhausted` siblings meaningful, and a
/// found row outside them would silently widen the searched space.
fn check_found_row_shape(
    row: &ShardRow,
    max_tail_terms: usize,
    certificate: &crate::gf2::IrreducibilityCertificate,
) -> Result<(), ShardError> {
    let exponents = certificate.polynomial.exponents();
    let derived_tail_terms = exponents.len().saturating_sub(1);
    if row.tail_terms != Some(derived_tail_terms) {
        return Err(ShardError::Artifact {
            degree: row.degree,
            error: format!(
                "row claims {:?} tail terms, the polynomial has {derived_tail_terms}",
                row.tail_terms
            ),
        });
    }
    if derived_tail_terms > max_tail_terms {
        return Err(ShardError::Artifact {
            degree: row.degree,
            error: format!(
                "{derived_tail_terms} tail terms exceeds the {max_tail_terms} sparse policy"
            ),
        });
    }
    if row.degree > 1
        && !exponents
            .iter()
            .all(|&exponent| exponent == row.degree || exponent <= row.degree / 2)
    {
        return Err(ShardError::Artifact {
            degree: row.degree,
            error: "polynomial leaves the searched half-degree window".to_owned(),
        });
    }
    if row.candidates_tested == 0 {
        return Err(ShardError::Artifact {
            degree: row.degree,
            error: "found row tested no candidates".to_owned(),
        });
    }
    Ok(())
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
    use crate::gf2::{Gf2Poly, certify_irreducible};

    /// A shard whose single negative row is a GENUINE exhaustion.
    ///
    /// Degree 8 with a trinomial-only policy is exhausted after exactly four
    /// candidates -- measured by running the producer, not asserted from a
    /// table.  Every adversarial fixture below perturbs exactly one field of
    /// this manifest, so nothing but the perturbed distinction separates
    /// acceptance from refusal.
    fn control() -> ShardManifest {
        ShardManifest {
            format: SHARD_FORMAT.to_owned(),
            version: SHARD_VERSION,
            producer: "test-producer".to_owned(),
            start_degree: 8,
            end_degree: 8,
            max_tail_terms: 2,
            max_candidates_per_degree: 100,
            arithmetic_limits: Gf2Limits::default().into(),
            rows: vec![ShardRow {
                degree: 8,
                status: ShardStatus::Exhausted,
                candidates_tested: 4,
                tail_terms: None,
                artifact: None,
                artifact_sha256: None,
            }],
        }
    }

    /// Write a manifest into a fresh lane-private directory and check it.
    fn check_manifest(
        label: &str,
        manifest: &ShardManifest,
        policy: ShardCheckPolicy,
    ) -> Result<ShardCheckSummary, ShardError> {
        let directory =
            std::env::temp_dir().join(format!("axeyum-gf2-shard-{label}-{}", std::process::id()));
        let _ = fs::remove_dir_all(&directory);
        fs::create_dir_all(&directory).expect("shard fixture directory");
        let json = to_canonical_manifest_json(manifest).expect("canonical fixture manifest");
        fs::write(directory.join(MANIFEST_FILE), json).expect("fixture manifest");
        let outcome = check_shard_directory_with_policy(&directory, policy);
        let _ = fs::remove_dir_all(&directory);
        outcome
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
        false_credit.rows[0].artifact = Some("degree-8.json".to_owned());
        assert!(matches!(
            to_canonical_manifest_json(&false_credit),
            Err(ShardError::Format(_))
        ));
    }

    /// The genuine exhaustion is admitted, and the summary says how much work
    /// the admission actually cost.  A run that re-derived nothing would report
    /// `rederived_candidates == 0`, which this pins against.
    #[test]
    fn genuine_exhaustion_is_admitted_and_charged() {
        let summary =
            check_manifest("genuine", &control(), ShardCheckPolicy::default()).expect("admitted");
        assert_eq!(summary.rows, 1);
        assert_eq!(summary.exhausted, 1);
        assert_eq!(summary.rederived_candidates, 4);
    }

    /// ADVERSARIAL. Degree 4 has the irreducible trinomial `x^4 + x + 1`, so an
    /// `Exhausted` row there is a fabricated negative theorem.  Every other
    /// field is well formed -- canonical JSON, complete ordered population, no
    /// evidence fields, and there is no artifact to hash -- so re-derivation is
    /// the ONLY thing standing between this manifest and a PASS.
    ///
    /// Before this repair the whole acceptance body was `summary.exhausted += 1`
    /// and this manifest passed.
    #[test]
    fn fabricated_exhaustion_is_refused() {
        let mut forged = control();
        forged.start_degree = 4;
        forged.end_degree = 4;
        forged.rows[0].degree = 4;
        forged.rows[0].candidates_tested = 1;
        let error = check_manifest("forged", &forged, ShardCheckPolicy::default())
            .expect_err("a fabricated exhaustion must not be admitted");
        let ShardError::Exhaustion { degree, error } = error else {
            panic!("expected a re-derivation failure, got {error:?}");
        };
        assert_eq!(degree, 4);
        assert!(
            error.contains("certified an irreducible candidate"),
            "{error}"
        );
    }

    /// ADVERSARIAL. The exhaustion itself is true; only the extent is inflated.
    /// The row claims five candidates where the producer's own enumeration tests
    /// four, so the receipt no longer describes the search it names.
    #[test]
    fn overstated_exhaustion_extent_is_refused() {
        let mut inflated = control();
        inflated.rows[0].candidates_tested = 5;
        let error = check_manifest("inflated", &inflated, ShardCheckPolicy::default())
            .expect_err("an inflated candidate count must not be admitted");
        assert!(
            matches!(&error, ShardError::Exhaustion { degree: 8, error } if error.contains("row claims 5")),
            "{error:?}"
        );
    }

    /// ADVERSARIAL. Widening the sparse policy makes the SAME degree-8 row false
    /// -- pentanomials reach further than trinomials -- while leaving the row
    /// byte-identical.  The distinction lives in `max_tail_terms`, which the row
    /// does not carry, and only re-derivation under the manifest's own declared
    /// policy can see it.
    #[test]
    fn exhaustion_is_relative_to_the_declared_sparse_policy() {
        let mut widened = control();
        widened.max_tail_terms = 4;
        let error = check_manifest("widened", &widened, ShardCheckPolicy::default())
            .expect_err("exhaustion under a wider policy is a different claim");
        assert!(
            matches!(error, ShardError::Exhaustion { degree: 8, .. }),
            "{error:?}"
        );
    }

    /// A budget too small to re-derive is a FAILURE, never an acceptance.  This
    /// is the guard against the repair degrading into the defect it replaces:
    /// if running out of budget silently admitted the row, the checker would be
    /// back to accepting exhaustion on the producer's word.
    #[test]
    fn an_unaffordable_rederivation_fails_rather_than_admits() {
        let policy = ShardCheckPolicy {
            max_rederived_candidates: 0,
            ..ShardCheckPolicy::default()
        };
        let error = check_manifest("nobudget", &control(), policy)
            .expect_err("an unchecked exhaustion must not be admitted");
        assert!(
            matches!(&error, ShardError::Exhaustion { degree: 8, error } if error.contains("budget")),
            "{error:?}"
        );
    }

    /// ADVERSARIAL. A `CandidateLimit` row asserts enumeration stopped AT the
    /// ceiling.  The producer returns the ceiling verbatim, so a row claiming a
    /// ceiling stop after testing nothing is contradicting the manifest it sits
    /// in -- and before this repair it was accepted as a free non-result.
    #[test]
    fn candidate_limit_row_must_sit_at_its_ceiling() {
        let mut manifest = control();
        manifest.max_candidates_per_degree = 2;
        manifest.rows[0].status = ShardStatus::CandidateLimit;
        manifest.rows[0].candidates_tested = 2;
        let summary = check_manifest("atlimit", &manifest, ShardCheckPolicy::default())
            .expect("a row at its ceiling is admitted");
        assert_eq!(summary.candidate_limit, 1);
        assert_eq!(summary.rederived_candidates, 0);

        let mut forged = manifest;
        forged.rows[0].candidates_tested = 0;
        let error = check_manifest("belowlimit", &forged, ShardCheckPolicy::default())
            .expect_err("a ceiling stop that tested nothing must not be admitted");
        assert!(
            matches!(&error, ShardError::Exhaustion { degree: 8, error } if error.contains("of a 2 ceiling")),
            "{error:?}"
        );
    }

    /// ADVERSARIAL, and DERIVED FROM THIS SUBJECT rather than copied from a
    /// sibling: `x^4 + x + 1` has exactly two nonleading terms, so 2 is the only
    /// admissible `tail_terms`, 3 is a forgery, and a one-term policy excludes
    /// it outright.  Both were unchecked before this repair -- `tail_terms` was
    /// required to be `Some`, never to be RIGHT.
    #[test]
    fn found_row_tail_terms_are_rederived_from_the_polynomial() {
        let limits = Gf2Limits::default();
        let polynomial = Gf2Poly::from_exponents(&[0, 1, 4], limits).unwrap();
        let certificate = certify_irreducible(&polynomial, limits)
            .unwrap()
            .expect("x^4 + x + 1 is irreducible");
        let honest = ShardRow {
            degree: 4,
            status: ShardStatus::Found,
            candidates_tested: 1,
            tail_terms: Some(2),
            artifact: Some("degree-4.json".to_owned()),
            artifact_sha256: Some("0".repeat(64)),
        };
        check_found_row_shape(&honest, 4, &certificate).expect("the honest row is admitted");

        let mut miscounted = honest.clone();
        miscounted.tail_terms = Some(3);
        assert!(
            check_found_row_shape(&miscounted, 4, &certificate).is_err(),
            "a forged tail-term count must not be admitted"
        );

        assert!(
            check_found_row_shape(&honest, 1, &certificate).is_err(),
            "a polynomial outside the declared sparse layers must not be admitted"
        );

        let mut untested = honest;
        untested.candidates_tested = 0;
        assert!(
            check_found_row_shape(&untested, 4, &certificate).is_err(),
            "a found row that tested no candidates must not be admitted"
        );
    }

    /// ADVERSARIAL. `x^8 + x^5 + x^3 + x + 1` is irreducible -- so every
    /// certificate check in the shard passes on it -- but exponent 5 exceeds
    /// 8/2 = 4, putting it outside the space the shard's `Exhausted` siblings
    /// are statements about.  Admitting it would silently widen every negative
    /// claim in the shard.  The in-window control is `x^8 + x^4 + x^3 + x^2 + 1`,
    /// which differs from it only in leaving the window alone.
    #[test]
    fn found_row_must_stay_in_the_searched_half_degree_window() {
        let limits = Gf2Limits::default();
        let row = |tail_terms| ShardRow {
            degree: 8,
            status: ShardStatus::Found,
            candidates_tested: 1,
            tail_terms: Some(tail_terms),
            artifact: Some("degree-8.json".to_owned()),
            artifact_sha256: Some("0".repeat(64)),
        };

        let in_window = Gf2Poly::from_exponents(&[0, 2, 3, 4, 8], limits).unwrap();
        let in_window = certify_irreducible(&in_window, limits)
            .unwrap()
            .expect("x^8 + x^4 + x^3 + x^2 + 1 is irreducible");
        check_found_row_shape(&row(4), 4, &in_window)
            .expect("an in-window witness of the same shape is admitted");

        let out_of_window = Gf2Poly::from_exponents(&[0, 1, 3, 5, 8], limits).unwrap();
        let out_of_window = certify_irreducible(&out_of_window, limits)
            .unwrap()
            .expect("x^8 + x^5 + x^3 + x + 1 is irreducible");
        assert!(
            check_found_row_shape(&row(4), 4, &out_of_window).is_err(),
            "a witness outside the half-degree window must not be admitted"
        );
    }

    #[test]
    fn sha256_is_stable() {
        assert_eq!(
            sha256_hex(b"abc"),
            "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
        );
    }
}
