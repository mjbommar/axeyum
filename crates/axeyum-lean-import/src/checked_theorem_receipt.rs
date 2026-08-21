//! Receipts for exact independently reconstructed theorem candidates.

use std::fmt;

use axeyum_lean_kernel::{Declaration, Kernel, NameId};
use serde_json::{Value, json};
use sha2::{Digest, Sha256};

use crate::{canonical_declaration_sha256, canonical_expression_sha256};

/// Schema for source-bound checked-candidate theorem receipts.
pub const CHECKED_SEMANTIC_THEOREM_RECEIPT_VERSION: &str =
    "axeyum-checked-semantic-theorem-receipt-v1";

/// Frozen authority a checked theorem must reproduce exactly.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CheckedTheoremAuthority {
    /// Caller-owned policy identity.
    pub policy_version: String,
    /// Exact source artifact identity.
    pub source_artifact_sha256: String,
    /// Exact source target name.
    pub target_definition: String,
    /// Exact fact-ledger identity.
    pub fact_id: String,
    /// Canonical theorem goal identity.
    pub goal_sha256: String,
    /// Sealed candidate observation identity.
    pub candidate_observation_sha256: String,
    /// Exact expected proof identity.
    pub expected_proof_sha256: String,
    /// Exact expected theorem declaration identity.
    pub expected_theorem_content_sha256: String,
    /// Frozen producer operation.
    pub operation: String,
    /// Maximum ordered plan templates.
    pub max_plan_templates: usize,
    /// Maximum kernel submissions.
    pub max_kernel_submissions: usize,
    /// Maximum executor invocations.
    pub max_executor_invocations: usize,
    /// Maximum producer retries.
    pub max_retries: usize,
}

/// Replayable evidence for one exact, source-bound, independently checked theorem.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CheckedSemanticTheoremReceipt {
    /// Stable receipt schema.
    pub schema_version: &'static str,
    /// Frozen authority reproduced by the theorem.
    pub authority: CheckedTheoremAuthority,
    /// Exact admitted theorem name.
    pub theorem_name: String,
    /// Canonical theorem declaration identity.
    pub theorem_content_sha256: String,
    /// Canonical theorem type identity.
    pub theorem_type_sha256: String,
    /// Canonical proof identity.
    pub proof_sha256: String,
    /// Version 1 requires an empty axiom footprint.
    pub axiom_footprint: Vec<String>,
    /// Version 1 requires no direct theorem dependencies.
    pub direct_theorem_dependencies: Vec<String>,
    /// Complete transitive theorem inventory, diagnostic only.
    pub transitive_theorem_dependencies: Vec<String>,
    /// Canonical digest of all preceding fields.
    pub receipt_sha256: String,
}

impl CheckedSemanticTheoremReceipt {
    /// Recompute and verify the receipt digest.
    #[must_use]
    pub fn has_valid_digest(&self) -> bool {
        serde_json::to_vec(&self.json_value(false))
            .is_ok_and(|payload| hex_sha256(&payload) == self.receipt_sha256)
    }

    /// Render stable pretty JSON for durable storage.
    ///
    /// # Errors
    ///
    /// Returns an error only if JSON serialization fails.
    pub fn to_pretty_json(&self) -> Result<String, serde_json::Error> {
        serde_json::to_string_pretty(&self.json_value(true)).map(|mut rendered| {
            rendered.push('\n');
            rendered
        })
    }

    fn json_value(&self, include_digest: bool) -> Value {
        let mut value = json!({
            "schema_version": self.schema_version,
            "authority": {
                "policy_version": self.authority.policy_version,
                "source_artifact_sha256": self.authority.source_artifact_sha256,
                "target_definition": self.authority.target_definition,
                "fact_id": self.authority.fact_id,
                "goal_sha256": self.authority.goal_sha256,
                "candidate_observation_sha256": self.authority.candidate_observation_sha256,
                "expected_proof_sha256": self.authority.expected_proof_sha256,
                "expected_theorem_content_sha256": self.authority.expected_theorem_content_sha256,
                "operation": self.authority.operation,
                "budget": {
                    "max_plan_templates": self.authority.max_plan_templates,
                    "max_kernel_submissions": self.authority.max_kernel_submissions,
                    "max_executor_invocations": self.authority.max_executor_invocations,
                    "max_retries": self.authority.max_retries,
                },
            },
            "theorem": {
                "name": self.theorem_name,
                "content_sha256": self.theorem_content_sha256,
                "type_sha256": self.theorem_type_sha256,
                "proof_sha256": self.proof_sha256,
            },
            "axiom_footprint": self.axiom_footprint,
            "diagnostic_dependencies": {
                "direct_theorems": self.direct_theorem_dependencies,
                "transitive_theorems": self.transitive_theorem_dependencies,
            },
        });
        if include_digest {
            value
                .as_object_mut()
                .expect("receipt JSON root is an object")
                .insert(
                    "receipt_sha256".to_owned(),
                    Value::String(self.receipt_sha256.clone()),
                );
        }
        value
    }
}

/// A checked theorem receipt could not be issued or replayed.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CheckedSemanticTheoremReceiptError {
    /// One authority string was empty or one digest was malformed.
    InvalidAuthority,
    /// The target was absent or was not a theorem.
    WrongTargetKind,
    /// The theorem did not reproduce the frozen candidate identities.
    CandidateMismatch,
    /// The theorem retained axioms.
    AxiomFootprint {
        /// Stable sorted rendered axiom names.
        names: Vec<String>,
    },
    /// The theorem directly depended on another theorem.
    TheoremDependencies {
        /// Stable sorted rendered direct theorem names.
        names: Vec<String>,
    },
    /// Canonical identity construction failed.
    Identity(String),
    /// A transported receipt was stale or mutated.
    ReceiptMismatch,
}

impl fmt::Display for CheckedSemanticTheoremReceiptError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidAuthority => write!(formatter, "checked theorem authority is invalid"),
            Self::WrongTargetKind => write!(formatter, "checked theorem target is not a theorem"),
            Self::CandidateMismatch => write!(formatter, "theorem differs from sealed candidate"),
            Self::AxiomFootprint { names } => {
                write!(
                    formatter,
                    "checked theorem retains axioms: {}",
                    names.join(",")
                )
            }
            Self::TheoremDependencies { names } => write!(
                formatter,
                "checked theorem directly depends on theorems: {}",
                names.join(",")
            ),
            Self::Identity(error) => write!(formatter, "checked theorem identity failed: {error}"),
            Self::ReceiptMismatch => write!(formatter, "checked theorem receipt changed"),
        }
    }
}

impl std::error::Error for CheckedSemanticTheoremReceiptError {}

/// Issue an exact receipt for an already independently admitted theorem.
///
/// # Errors
///
/// Fails closed on malformed authority, candidate identity drift, a non-theorem
/// target, axioms, direct theorem dependencies, or identity construction failure.
pub fn issue_checked_semantic_theorem_receipt(
    kernel: &mut Kernel,
    theorem_name: NameId,
    authority: &CheckedTheoremAuthority,
) -> Result<CheckedSemanticTheoremReceipt, CheckedSemanticTheoremReceiptError> {
    validate_authority(authority)?;
    let Some(Declaration::Theorem { ty, value, .. }) = kernel.environment().get(theorem_name)
    else {
        return Err(CheckedSemanticTheoremReceiptError::WrongTargetKind);
    };
    let (ty, value) = (*ty, *value);
    let theorem_type_sha256 = canonical_expression_sha256(kernel, ty)
        .map_err(CheckedSemanticTheoremReceiptError::Identity)?;
    let proof_sha256 = canonical_expression_sha256(kernel, value)
        .map_err(CheckedSemanticTheoremReceiptError::Identity)?;
    let theorem_content_sha256 = canonical_declaration_sha256(kernel, theorem_name)
        .map_err(CheckedSemanticTheoremReceiptError::Identity)?;
    if theorem_type_sha256 != authority.goal_sha256
        || proof_sha256 != authority.expected_proof_sha256
        || theorem_content_sha256 != authority.expected_theorem_content_sha256
    {
        return Err(CheckedSemanticTheoremReceiptError::CandidateMismatch);
    }
    let axiom_footprint = rendered_names(kernel, &kernel.axiom_footprint(theorem_name));
    if !axiom_footprint.is_empty() {
        return Err(CheckedSemanticTheoremReceiptError::AxiomFootprint {
            names: axiom_footprint,
        });
    }
    let direct_theorem_dependencies =
        rendered_names(kernel, &kernel.theorem_dependencies(theorem_name));
    if !direct_theorem_dependencies.is_empty() {
        return Err(CheckedSemanticTheoremReceiptError::TheoremDependencies {
            names: direct_theorem_dependencies,
        });
    }
    let transitive_theorem_dependencies = rendered_names(
        kernel,
        &kernel
            .declaration_dependency_closure(theorem_name)
            .into_iter()
            .filter(|name| {
                *name != theorem_name
                    && matches!(
                        kernel.environment().get(*name),
                        Some(Declaration::Theorem { .. })
                    )
            })
            .collect::<Vec<_>>(),
    );
    let mut receipt = CheckedSemanticTheoremReceipt {
        schema_version: CHECKED_SEMANTIC_THEOREM_RECEIPT_VERSION,
        authority: authority.clone(),
        theorem_name: kernel.display_name(theorem_name).to_string(),
        theorem_content_sha256,
        theorem_type_sha256,
        proof_sha256,
        axiom_footprint,
        direct_theorem_dependencies,
        transitive_theorem_dependencies,
        receipt_sha256: String::new(),
    };
    let payload = serde_json::to_vec(&receipt.json_value(false))
        .map_err(|error| CheckedSemanticTheoremReceiptError::Identity(error.to_string()))?;
    receipt.receipt_sha256 = hex_sha256(&payload);
    Ok(receipt)
}

/// Reissue and compare a checked theorem receipt exactly.
///
/// # Errors
///
/// Returns the issue-time error or `ReceiptMismatch` for stale or mutated evidence.
pub fn verify_checked_semantic_theorem_receipt(
    receipt: &CheckedSemanticTheoremReceipt,
    kernel: &mut Kernel,
    theorem_name: NameId,
    authority: &CheckedTheoremAuthority,
) -> Result<(), CheckedSemanticTheoremReceiptError> {
    if !receipt.has_valid_digest() {
        return Err(CheckedSemanticTheoremReceiptError::ReceiptMismatch);
    }
    let reissued = issue_checked_semantic_theorem_receipt(kernel, theorem_name, authority)?;
    if &reissued != receipt {
        return Err(CheckedSemanticTheoremReceiptError::ReceiptMismatch);
    }
    Ok(())
}

/// Schema for checked theorem receipts whose direct library premises are
/// explicitly preregistered by name and canonical declaration identity.
pub const CHECKED_DEPENDENCY_THEOREM_RECEIPT_VERSION: &str =
    "axeyum-checked-dependency-theorem-receipt-v1";

/// One exact direct theorem premise authorized for a dependency-bound receipt.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CheckedTheoremDependency {
    /// Stable rendered theorem name.
    pub name: String,
    /// Canonical declaration identity, which recursively binds its dependencies.
    pub content_sha256: String,
}

/// Frozen authority for a checked theorem with explicit library premises.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CheckedDependencyTheoremAuthority {
    /// Exact source, candidate, operation, and budget authority.
    pub theorem: CheckedTheoremAuthority,
    /// Complete sorted direct theorem premise set.
    pub expected_direct_theorem_dependencies: Vec<CheckedTheoremDependency>,
}

/// Replayable evidence for an exact theorem and its preregistered direct premises.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CheckedDependencyTheoremReceipt {
    /// Stable receipt schema.
    pub schema_version: &'static str,
    /// Frozen authority reproduced by the theorem and dependency set.
    pub authority: CheckedDependencyTheoremAuthority,
    /// Exact admitted theorem name.
    pub theorem_name: String,
    /// Canonical theorem declaration identity.
    pub theorem_content_sha256: String,
    /// Canonical theorem type identity.
    pub theorem_type_sha256: String,
    /// Canonical proof identity.
    pub proof_sha256: String,
    /// Must remain empty across the complete declaration closure.
    pub axiom_footprint: Vec<String>,
    /// Exact direct theorem premises and their canonical declaration identities.
    pub direct_theorem_dependencies: Vec<CheckedTheoremDependency>,
    /// Complete transitive theorem inventory, bound by replay but not premise authority.
    pub transitive_theorem_dependencies: Vec<CheckedTheoremDependency>,
    /// Canonical digest of all preceding fields.
    pub receipt_sha256: String,
}

impl CheckedDependencyTheoremReceipt {
    /// Recompute and verify the receipt digest.
    #[must_use]
    pub fn has_valid_digest(&self) -> bool {
        serde_json::to_vec(&self.json_value(false))
            .is_ok_and(|payload| hex_sha256(&payload) == self.receipt_sha256)
    }

    /// Render stable pretty JSON for durable storage.
    ///
    /// # Errors
    ///
    /// Returns an error only if JSON serialization fails.
    pub fn to_pretty_json(&self) -> Result<String, serde_json::Error> {
        serde_json::to_string_pretty(&self.json_value(true)).map(|mut rendered| {
            rendered.push('\n');
            rendered
        })
    }

    fn json_value(&self, include_digest: bool) -> Value {
        let dependency_json = |rows: &[CheckedTheoremDependency]| {
            rows.iter()
                .map(|row| {
                    json!({
                        "name": row.name,
                        "content_sha256": row.content_sha256,
                    })
                })
                .collect::<Vec<_>>()
        };
        let base = &self.authority.theorem;
        let mut value = json!({
            "schema_version": self.schema_version,
            "authority": {
                "policy_version": base.policy_version,
                "source_artifact_sha256": base.source_artifact_sha256,
                "target_definition": base.target_definition,
                "fact_id": base.fact_id,
                "goal_sha256": base.goal_sha256,
                "candidate_observation_sha256": base.candidate_observation_sha256,
                "expected_proof_sha256": base.expected_proof_sha256,
                "expected_theorem_content_sha256": base.expected_theorem_content_sha256,
                "operation": base.operation,
                "budget": {
                    "max_plan_templates": base.max_plan_templates,
                    "max_kernel_submissions": base.max_kernel_submissions,
                    "max_executor_invocations": base.max_executor_invocations,
                    "max_retries": base.max_retries,
                },
                "expected_direct_theorem_dependencies":
                    dependency_json(&self.authority.expected_direct_theorem_dependencies),
            },
            "theorem": {
                "name": self.theorem_name,
                "content_sha256": self.theorem_content_sha256,
                "type_sha256": self.theorem_type_sha256,
                "proof_sha256": self.proof_sha256,
            },
            "axiom_footprint": self.axiom_footprint,
            "dependencies": {
                "direct_theorems": dependency_json(&self.direct_theorem_dependencies),
                "transitive_theorems": dependency_json(&self.transitive_theorem_dependencies),
            },
        });
        if include_digest {
            value
                .as_object_mut()
                .expect("receipt JSON root is an object")
                .insert(
                    "receipt_sha256".to_owned(),
                    Value::String(self.receipt_sha256.clone()),
                );
        }
        value
    }
}

/// A dependency-bound checked theorem receipt could not be issued or replayed.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CheckedDependencyTheoremReceiptError {
    /// Base authority or the expected dependency set is malformed.
    InvalidAuthority,
    /// The target was absent or was not a theorem.
    WrongTargetKind,
    /// The theorem did not reproduce the frozen candidate identities.
    CandidateMismatch,
    /// The theorem's complete closure retained axioms.
    AxiomFootprint {
        /// Stable sorted rendered axiom names.
        names: Vec<String>,
    },
    /// The observed direct premise set differed from preregistered authority.
    DependencyMismatch {
        /// Complete preregistered rows.
        expected: Vec<CheckedTheoremDependency>,
        /// Complete kernel-observed rows.
        observed: Vec<CheckedTheoremDependency>,
    },
    /// Canonical identity construction failed.
    Identity(String),
    /// A transported receipt was stale or mutated.
    ReceiptMismatch,
}

impl fmt::Display for CheckedDependencyTheoremReceiptError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidAuthority => {
                write!(formatter, "checked dependency theorem authority is invalid")
            }
            Self::WrongTargetKind => write!(formatter, "checked theorem target is not a theorem"),
            Self::CandidateMismatch => write!(formatter, "theorem differs from sealed candidate"),
            Self::AxiomFootprint { names } => {
                write!(
                    formatter,
                    "checked theorem retains axioms: {}",
                    names.join(",")
                )
            }
            Self::DependencyMismatch { expected, observed } => write!(
                formatter,
                "checked theorem dependencies differ: expected {expected:?}; observed {observed:?}"
            ),
            Self::Identity(error) => write!(formatter, "checked theorem identity failed: {error}"),
            Self::ReceiptMismatch => write!(formatter, "checked theorem receipt changed"),
        }
    }
}

impl std::error::Error for CheckedDependencyTheoremReceiptError {}

/// Issue an exact receipt for an independently admitted theorem whose direct
/// theorem premises have all been preregistered.
///
/// # Errors
///
/// Fails closed on malformed authority, candidate identity drift, a non-theorem
/// target, any reached axiom, direct dependency drift, or identity failure.
pub fn issue_checked_dependency_theorem_receipt(
    kernel: &mut Kernel,
    theorem_name: NameId,
    authority: &CheckedDependencyTheoremAuthority,
) -> Result<CheckedDependencyTheoremReceipt, CheckedDependencyTheoremReceiptError> {
    validate_dependency_authority(authority)?;
    let Some(Declaration::Theorem { ty, value, .. }) = kernel.environment().get(theorem_name)
    else {
        return Err(CheckedDependencyTheoremReceiptError::WrongTargetKind);
    };
    let (ty, value) = (*ty, *value);
    let theorem_type_sha256 = canonical_expression_sha256(kernel, ty)
        .map_err(CheckedDependencyTheoremReceiptError::Identity)?;
    let proof_sha256 = canonical_expression_sha256(kernel, value)
        .map_err(CheckedDependencyTheoremReceiptError::Identity)?;
    let theorem_content_sha256 = canonical_declaration_sha256(kernel, theorem_name)
        .map_err(CheckedDependencyTheoremReceiptError::Identity)?;
    let base = &authority.theorem;
    if theorem_type_sha256 != base.goal_sha256
        || proof_sha256 != base.expected_proof_sha256
        || theorem_content_sha256 != base.expected_theorem_content_sha256
    {
        return Err(CheckedDependencyTheoremReceiptError::CandidateMismatch);
    }
    let axiom_footprint = rendered_names(kernel, &kernel.axiom_footprint(theorem_name));
    if !axiom_footprint.is_empty() {
        return Err(CheckedDependencyTheoremReceiptError::AxiomFootprint {
            names: axiom_footprint,
        });
    }
    let direct_theorem_dependencies =
        dependency_rows(kernel, &kernel.theorem_dependencies(theorem_name))?;
    if direct_theorem_dependencies != authority.expected_direct_theorem_dependencies {
        return Err(CheckedDependencyTheoremReceiptError::DependencyMismatch {
            expected: authority.expected_direct_theorem_dependencies.clone(),
            observed: direct_theorem_dependencies,
        });
    }
    let transitive_names = kernel
        .declaration_dependency_closure(theorem_name)
        .into_iter()
        .filter(|name| {
            *name != theorem_name
                && matches!(
                    kernel.environment().get(*name),
                    Some(Declaration::Theorem { .. })
                )
        })
        .collect::<Vec<_>>();
    let transitive_theorem_dependencies = dependency_rows(kernel, &transitive_names)?;
    let mut receipt = CheckedDependencyTheoremReceipt {
        schema_version: CHECKED_DEPENDENCY_THEOREM_RECEIPT_VERSION,
        authority: authority.clone(),
        theorem_name: kernel.display_name(theorem_name).to_string(),
        theorem_content_sha256,
        theorem_type_sha256,
        proof_sha256,
        axiom_footprint,
        direct_theorem_dependencies: authority.expected_direct_theorem_dependencies.clone(),
        transitive_theorem_dependencies,
        receipt_sha256: String::new(),
    };
    let payload = serde_json::to_vec(&receipt.json_value(false))
        .map_err(|error| CheckedDependencyTheoremReceiptError::Identity(error.to_string()))?;
    receipt.receipt_sha256 = hex_sha256(&payload);
    Ok(receipt)
}

/// Reissue and compare a dependency-bound checked theorem receipt exactly.
///
/// # Errors
///
/// Returns the issue-time error or `ReceiptMismatch` for stale or mutated evidence.
pub fn verify_checked_dependency_theorem_receipt(
    receipt: &CheckedDependencyTheoremReceipt,
    kernel: &mut Kernel,
    theorem_name: NameId,
    authority: &CheckedDependencyTheoremAuthority,
) -> Result<(), CheckedDependencyTheoremReceiptError> {
    if !receipt.has_valid_digest() {
        return Err(CheckedDependencyTheoremReceiptError::ReceiptMismatch);
    }
    let reissued = issue_checked_dependency_theorem_receipt(kernel, theorem_name, authority)?;
    if &reissued != receipt {
        return Err(CheckedDependencyTheoremReceiptError::ReceiptMismatch);
    }
    Ok(())
}

fn validate_dependency_authority(
    authority: &CheckedDependencyTheoremAuthority,
) -> Result<(), CheckedDependencyTheoremReceiptError> {
    validate_authority(&authority.theorem)
        .map_err(|_| CheckedDependencyTheoremReceiptError::InvalidAuthority)?;
    let dependencies = &authority.expected_direct_theorem_dependencies;
    if dependencies.is_empty()
        || dependencies
            .windows(2)
            .any(|rows| rows[0].name >= rows[1].name)
        || dependencies
            .iter()
            .any(|row| row.name.is_empty() || !is_sha256(&row.content_sha256))
    {
        return Err(CheckedDependencyTheoremReceiptError::InvalidAuthority);
    }
    Ok(())
}

fn dependency_rows(
    kernel: &mut Kernel,
    names: &[NameId],
) -> Result<Vec<CheckedTheoremDependency>, CheckedDependencyTheoremReceiptError> {
    let mut rows = names
        .iter()
        .map(|&name| {
            canonical_declaration_sha256(kernel, name)
                .map(|content_sha256| CheckedTheoremDependency {
                    name: kernel.display_name(name).to_string(),
                    content_sha256,
                })
                .map_err(CheckedDependencyTheoremReceiptError::Identity)
        })
        .collect::<Result<Vec<_>, _>>()?;
    rows.sort_by(|left, right| left.name.cmp(&right.name));
    if rows.windows(2).any(|pair| pair[0].name == pair[1].name) {
        return Err(CheckedDependencyTheoremReceiptError::Identity(
            "duplicate rendered theorem dependency name".to_owned(),
        ));
    }
    Ok(rows)
}

fn validate_authority(
    authority: &CheckedTheoremAuthority,
) -> Result<(), CheckedSemanticTheoremReceiptError> {
    let strings = [
        authority.policy_version.as_str(),
        authority.target_definition.as_str(),
        authority.fact_id.as_str(),
        authority.operation.as_str(),
    ];
    let digests = [
        authority.source_artifact_sha256.as_str(),
        authority.goal_sha256.as_str(),
        authority.candidate_observation_sha256.as_str(),
        authority.expected_proof_sha256.as_str(),
        authority.expected_theorem_content_sha256.as_str(),
    ];
    if strings.iter().any(|value| value.is_empty())
        || digests.iter().any(|value| !is_sha256(value))
        || authority.max_plan_templates == 0
        || authority.max_kernel_submissions == 0
        || authority.max_executor_invocations == 0
    {
        return Err(CheckedSemanticTheoremReceiptError::InvalidAuthority);
    }
    Ok(())
}

fn is_sha256(value: &str) -> bool {
    value.len() == 64 && value.bytes().all(|byte| byte.is_ascii_hexdigit())
}

fn rendered_names(kernel: &Kernel, names: &[NameId]) -> Vec<String> {
    let mut rendered: Vec<_> = names
        .iter()
        .map(|&name| kernel.display_name(name).to_string())
        .collect();
    rendered.sort();
    rendered.dedup();
    rendered
}

fn hex_sha256(bytes: &[u8]) -> String {
    let digest = Sha256::digest(bytes);
    let mut output = String::with_capacity(64);
    for byte in digest {
        use std::fmt::Write;
        write!(output, "{byte:02x}").expect("writing to String cannot fail");
    }
    output
}
