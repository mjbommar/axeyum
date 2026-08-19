//! Durable identity receipt for one checked proof-free type slice.

use std::collections::HashMap;
use std::fmt;

use axeyum_lean_kernel::{
    AutoParamTypeNormalizationReport, Declaration, ExprId, ExprNode, Kernel, NameId,
};
use serde_json::{Value, json};
use sha2::{Digest, Sha256};

use crate::{
    CompletedStatementImport, DeclarationKind, GeneralizedGoal, ImportReport, TypeSliceError,
    canonical_declaration_sha256, canonical_expression_sha256, canonical_level_sha256,
    verify_generalized_specialization,
};

/// Receipt schema emitted by [`issue_type_slice_receipt`].
pub const TYPE_SLICE_RECEIPT_VERSION: &str = "axeyum-proof-free-type-slice-receipt-v1";
/// Receipt schema for ADR-0485 checked type-only `autoParam` transport.
pub const NORMALIZED_TYPE_SLICE_RECEIPT_VERSION: &str = "axeyum-proof-free-type-slice-receipt-v2";

/// One source declaration and its independently admitted normalized identity.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TypeSliceNormalizedDeclarationReceipt {
    /// Exact rendered declaration name.
    pub name: String,
    /// Canonical complete source declaration identity.
    pub source_content_sha256: String,
    /// Canonical complete normalized fresh declaration identity.
    pub normalized_content_sha256: String,
    /// Canonical normalized direct-dependency binding identity.
    pub normalized_dependency_sha256: String,
}

/// Checked type-only normalization bound into a v2 slice receipt.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TypeSliceTransportNormalizationReceipt {
    /// Canonical source declaration identity of Lean 4.30's `autoParam` abbrev.
    pub auto_param_source_content_sha256: String,
    /// Unique saturated annotations rewritten across selected declaration types.
    pub rewritten_occurrences: usize,
    /// Every changed declaration, sorted by rendered name.
    pub declarations: Vec<TypeSliceNormalizedDeclarationReceipt>,
}

/// Source stream and exact target identity bound by a type-slice receipt.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TypeSliceSourceReceipt {
    /// SHA-256 supplied for the complete source NDJSON byte stream.
    pub stream_sha256: String,
    /// `lean4export` wire-format version from the completed import.
    pub format_version: String,
    /// Official Lean version from the independently completed import.
    pub lean_version: String,
    /// Official Lean source hash from the independently completed import.
    pub lean_githash: String,
    /// Exporter version from the independently completed import.
    pub exporter_version: String,
    /// Canonical declaration-identity schema used by the source manifest.
    pub declaration_identity_version: String,
    /// Exact rendered target declaration name.
    pub target: String,
    /// Canonical structural identity of the source target declaration.
    pub target_content_sha256: String,
    /// Canonical identity of the original proposition expression.
    pub goal_sha256: String,
}

/// One exact abstraction identity and its checked source occurrence count.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TypeSliceAbstractionReceipt {
    /// Outer-to-inner binder position.
    pub binder_position: usize,
    /// Exact rendered source declaration name.
    pub source_name: String,
    /// Canonical structural identity of that source declaration.
    pub source_content_sha256: String,
    /// Canonical identities of the exact universe arguments, in order.
    pub universe_sha256: Vec<String>,
    /// Canonical identity of the instantiated, pre-generalization source type.
    pub instantiated_type_sha256: String,
    /// Expanded structural occurrences across the source goal and all selected
    /// instantiated binder types.
    pub source_occurrences: u64,
}

/// One declaration retained in the fresh producer environment.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TypeSliceRetainedReceipt {
    /// Exact rendered declaration name.
    pub name: String,
    /// Stable declaration kind.
    pub kind: String,
    /// Canonical structural declaration identity.
    pub content_sha256: String,
    /// Canonical direct-dependency binding identity.
    pub dependency_sha256: String,
}

/// Durable result of checked generalization, fresh-kernel transport, and exact
/// specialization.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TypeSliceReceipt {
    /// Stable receipt schema.
    pub schema_version: &'static str,
    /// Frozen caller-owned selection policy identifier.
    pub policy_version: String,
    /// Source stream, toolchain, target, and proposition identity.
    pub source: TypeSliceSourceReceipt,
    /// Canonical generalized proposition identity in the source kernel.
    pub sliced_goal_sha256: String,
    /// Canonical target-definition identity in the fresh kernel.
    pub fresh_target_content_sha256: String,
    /// Exact abstraction identities in binder order.
    pub abstractions: Vec<TypeSliceAbstractionReceipt>,
    /// Complete canonically ordered fresh producer environment.
    pub retained: Vec<TypeSliceRetainedReceipt>,
    /// Present only for the v2 checked type-only transport route.
    pub transport_normalization: Option<TypeSliceTransportNormalizationReceipt>,
    /// True only after the kernel accepted exact specialization.
    pub specialization_verified: bool,
    /// SHA-256 of the canonical compact receipt payload excluding this field.
    pub receipt_sha256: String,
}

impl TypeSliceReceipt {
    /// Recompute the canonical payload digest after transport or mutation.
    #[must_use]
    pub fn has_valid_digest(&self) -> bool {
        serde_json::to_vec(&self.json_value(false))
            .is_ok_and(|payload| hex_sha256(&payload) == self.receipt_sha256)
    }

    /// Render a stable pretty JSON object suitable for external durable storage.
    ///
    /// # Errors
    ///
    /// Returns a serialization diagnostic if JSON rendering fails.
    pub fn to_pretty_json(&self) -> Result<String, serde_json::Error> {
        serde_json::to_string_pretty(&self.json_value(true)).map(|mut value| {
            value.push('\n');
            value
        })
    }

    fn json_value(&self, include_digest: bool) -> Value {
        let abstractions: Vec<_> = self
            .abstractions
            .iter()
            .map(|binding| {
                json!({
                    "binder_position": binding.binder_position,
                    "source_name": binding.source_name,
                    "source_content_sha256": binding.source_content_sha256,
                    "universe_sha256": binding.universe_sha256,
                    "instantiated_type_sha256": binding.instantiated_type_sha256,
                    "source_occurrences": binding.source_occurrences,
                })
            })
            .collect();
        let retained: Vec<_> = self
            .retained
            .iter()
            .map(|declaration| {
                json!({
                    "name": declaration.name,
                    "kind": declaration.kind,
                    "content_sha256": declaration.content_sha256,
                    "dependency_sha256": declaration.dependency_sha256,
                })
            })
            .collect();
        let mut value = json!({
            "schema_version": self.schema_version,
            "policy_version": self.policy_version,
            "source": {
                "stream_sha256": self.source.stream_sha256,
                "format_version": self.source.format_version,
                "lean_version": self.source.lean_version,
                "lean_githash": self.source.lean_githash,
                "exporter_version": self.source.exporter_version,
                "declaration_identity_version": self.source.declaration_identity_version,
                "target": self.source.target,
                "target_content_sha256": self.source.target_content_sha256,
                "goal_sha256": self.source.goal_sha256,
            },
            "sliced_goal_sha256": self.sliced_goal_sha256,
            "fresh_target_content_sha256": self.fresh_target_content_sha256,
            "abstractions": abstractions,
            "retained": retained,
            "specialization_verified": self.specialization_verified,
        });
        if let Some(normalization) = &self.transport_normalization {
            let declarations: Vec<_> = normalization
                .declarations
                .iter()
                .map(|declaration| {
                    json!({
                        "name": declaration.name,
                        "source_content_sha256": declaration.source_content_sha256,
                        "normalized_content_sha256": declaration.normalized_content_sha256,
                        "normalized_dependency_sha256": declaration.normalized_dependency_sha256,
                    })
                })
                .collect();
            value
                .as_object_mut()
                .expect("receipt JSON root is an object")
                .insert(
                    "transport_normalization".to_owned(),
                    json!({
                        "kind": "checked-auto-param-type-only-v1",
                        "auto_param_source_content_sha256": normalization.auto_param_source_content_sha256,
                        "rewritten_occurrences": normalization.rewritten_occurrences,
                        "declarations": declarations,
                    }),
                );
        }
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

/// A receipt could not be issued from the supplied checked objects.
#[derive(Debug)]
pub enum TypeSliceReceiptError {
    /// The selection policy identifier was empty.
    EmptyPolicy,
    /// The supplied source-stream digest was not lowercase hexadecimal SHA-256.
    InvalidSourceDigest,
    /// The source target did not have exactly one matching identity.
    SourceTargetIdentity {
        /// Rendered target name.
        name: String,
        /// Number of matching identities.
        observed: usize,
    },
    /// The source target was not a monomorphic transparent goal definition.
    SourceTargetNotDefinition,
    /// The supplied source goal was not the source target's exact value.
    SourceGoalNotTargetValue,
    /// A report content identity disagreed with the supplied source kernel.
    SourceContentIdentityMismatch {
        /// Rendered declaration name.
        name: String,
    },
    /// An abstraction's source declaration identity was absent or repeated.
    SourceDeclarationIdentity {
        /// Rendered declaration name.
        name: String,
        /// Number of matching identities.
        observed: usize,
    },
    /// A specialization argument was not the exact bound source constant.
    ArgumentNotExactSourceConstant {
        /// Zero-based binder position.
        index: usize,
    },
    /// The fresh goal differed from the generalized source-kernel goal.
    FreshGoalIdentityMismatch,
    /// The fresh environment unexpectedly contained a trusted declaration.
    TrustedFreshDeclaration {
        /// Rendered declaration name.
        name: String,
        /// Stable declaration kind.
        kind: DeclarationKind,
    },
    /// A supplied checked normalization report was empty or internally
    /// inconsistent with the source and fresh identity manifests.
    NormalizationIdentity {
        /// Stable diagnostic.
        reason: String,
    },
    /// Expanded occurrence counting exceeded `u64`.
    OccurrenceOverflow,
    /// Canonical identity construction failed.
    Identity(String),
    /// The underlying generalization/specialization contract failed.
    Slice(TypeSliceError),
}

impl fmt::Display for TypeSliceReceiptError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::EmptyPolicy => write!(f, "type-slice policy version is empty"),
            Self::InvalidSourceDigest => write!(f, "source digest is not lowercase SHA-256"),
            Self::SourceTargetIdentity { name, observed } => write!(
                f,
                "source target {name} has {observed} declaration identities"
            ),
            Self::SourceTargetNotDefinition => {
                write!(
                    f,
                    "source target is not a monomorphic transparent definition"
                )
            }
            Self::SourceGoalNotTargetValue => {
                write!(f, "source goal is not the exact source target value")
            }
            Self::SourceContentIdentityMismatch { name } => {
                write!(f, "source report content identity disagrees for {name}")
            }
            Self::SourceDeclarationIdentity { name, observed } => write!(
                f,
                "source abstraction {name} has {observed} declaration identities"
            ),
            Self::ArgumentNotExactSourceConstant { index } => write!(
                f,
                "specialization argument {index} is not its exact source constant"
            ),
            Self::FreshGoalIdentityMismatch => {
                write!(
                    f,
                    "fresh-kernel goal identity differs from generalized goal"
                )
            }
            Self::TrustedFreshDeclaration { name, kind } => {
                write!(f, "fresh environment retained trusted {kind:?} {name}")
            }
            Self::NormalizationIdentity { reason } => {
                write!(f, "transport normalization identity failed: {reason}")
            }
            Self::OccurrenceOverflow => write!(f, "source occurrence count overflowed u64"),
            Self::Identity(error) => write!(f, "canonical identity failed: {error}"),
            Self::Slice(error) => write!(f, "type-slice check failed: {error}"),
        }
    }
}

impl std::error::Error for TypeSliceReceiptError {}

impl From<TypeSliceError> for TypeSliceReceiptError {
    fn from(error: TypeSliceError) -> Self {
        Self::Slice(error)
    }
}

/// Issue one content-addressed receipt after checking source bindings,
/// fresh-kernel identity, proof isolation, and exact specialization.
///
/// `source_stream_sha256` is bound as supplied provenance. A replay checker must
/// recompute it from the external source bytes before calling this operation.
///
/// # Errors
///
/// Returns [`TypeSliceReceiptError`] on any identity mismatch, trusted fresh
/// declaration, inexact source argument, specialization failure, or malformed
/// provenance.
#[allow(clippy::too_many_arguments, clippy::too_many_lines)]
pub fn issue_type_slice_receipt(
    source_kernel: &mut Kernel,
    source_report: &ImportReport,
    source_stream_sha256: &str,
    source_target: NameId,
    source_goal: ExprId,
    generalized: &GeneralizedGoal,
    source_arguments: &[ExprId],
    fresh: &CompletedStatementImport,
    policy_version: &str,
) -> Result<TypeSliceReceipt, TypeSliceReceiptError> {
    issue_type_slice_receipt_internal(
        source_kernel,
        source_report,
        source_stream_sha256,
        source_target,
        source_goal,
        generalized,
        source_arguments,
        fresh,
        policy_version,
        None,
    )
}

/// Issue a v2 receipt that additionally binds one checked type-only
/// `autoParam` normalization report to source and fresh declaration identities.
///
/// # Errors
///
/// Returns the v1 receipt errors or [`TypeSliceReceiptError::NormalizationIdentity`].
#[allow(clippy::too_many_arguments)]
pub fn issue_type_slice_receipt_with_auto_param_normalization(
    source_kernel: &mut Kernel,
    source_report: &ImportReport,
    source_stream_sha256: &str,
    source_target: NameId,
    source_goal: ExprId,
    generalized: &GeneralizedGoal,
    source_arguments: &[ExprId],
    fresh: &CompletedStatementImport,
    policy_version: &str,
    normalization: &AutoParamTypeNormalizationReport,
) -> Result<TypeSliceReceipt, TypeSliceReceiptError> {
    issue_type_slice_receipt_internal(
        source_kernel,
        source_report,
        source_stream_sha256,
        source_target,
        source_goal,
        generalized,
        source_arguments,
        fresh,
        policy_version,
        Some(normalization),
    )
}

#[allow(clippy::too_many_arguments, clippy::too_many_lines)]
fn issue_type_slice_receipt_internal(
    source_kernel: &mut Kernel,
    source_report: &ImportReport,
    source_stream_sha256: &str,
    source_target: NameId,
    source_goal: ExprId,
    generalized: &GeneralizedGoal,
    source_arguments: &[ExprId],
    fresh: &CompletedStatementImport,
    policy_version: &str,
    normalization: Option<&AutoParamTypeNormalizationReport>,
) -> Result<TypeSliceReceipt, TypeSliceReceiptError> {
    if policy_version.is_empty() {
        return Err(TypeSliceReceiptError::EmptyPolicy);
    }
    if !is_sha256(source_stream_sha256) {
        return Err(TypeSliceReceiptError::InvalidSourceDigest);
    }
    let source_target_name = source_kernel.display_name(source_target).to_string();
    let source_target_matches: Vec<_> = source_report
        .declaration_identities
        .iter()
        .filter(|identity| identity.name == source_target_name)
        .collect();
    if source_target_matches.len() != 1 {
        return Err(TypeSliceReceiptError::SourceTargetIdentity {
            name: source_target_name,
            observed: source_target_matches.len(),
        });
    }
    let Some(Declaration::Definition { uparams, value, .. }) =
        source_kernel.environment().get(source_target)
    else {
        return Err(TypeSliceReceiptError::SourceTargetNotDefinition);
    };
    if !uparams.is_empty() {
        return Err(TypeSliceReceiptError::SourceTargetNotDefinition);
    }
    if *value != source_goal {
        return Err(TypeSliceReceiptError::SourceGoalNotTargetValue);
    }
    let source_target_content = canonical_declaration_sha256(source_kernel, source_target)
        .map_err(TypeSliceReceiptError::Identity)?;
    if source_target_content != source_target_matches[0].content_sha256 {
        return Err(TypeSliceReceiptError::SourceContentIdentityMismatch {
            name: source_target_name,
        });
    }
    if source_arguments.len() != generalized.binders.len() {
        verify_generalized_specialization(
            source_kernel,
            generalized,
            source_arguments,
            source_goal,
        )?;
    }
    for (index, (binder, &argument)) in generalized.binders.iter().zip(source_arguments).enumerate()
    {
        if !matches!(
            source_kernel.expr_node(argument),
            ExprNode::Const(name, levels)
                if *name == binder.source.name && *levels == binder.source.levels
        ) {
            return Err(TypeSliceReceiptError::ArgumentNotExactSourceConstant { index });
        }
    }
    verify_generalized_specialization(source_kernel, generalized, source_arguments, source_goal)?;

    let source_goal_sha256 = canonical_expression_sha256(source_kernel, source_goal)
        .map_err(TypeSliceReceiptError::Identity)?;
    let sliced_goal_sha256 = canonical_expression_sha256(source_kernel, generalized.goal)
        .map_err(TypeSliceReceiptError::Identity)?;
    let fresh_goal_sha256 = canonical_expression_sha256(fresh.kernel(), fresh.goal())
        .map_err(TypeSliceReceiptError::Identity)?;
    if fresh_goal_sha256 != sliced_goal_sha256 {
        return Err(TypeSliceReceiptError::FreshGoalIdentityMismatch);
    }

    let fresh_target_name = fresh.kernel().display_name(fresh.target_name()).to_string();
    let fresh_target_matches: Vec<_> = fresh
        .report()
        .declaration_identities
        .iter()
        .filter(|identity| identity.name == fresh_target_name)
        .collect();
    if fresh_target_matches.len() != 1 {
        return Err(TypeSliceReceiptError::SourceTargetIdentity {
            name: fresh_target_name,
            observed: fresh_target_matches.len(),
        });
    }

    let mut retained = Vec::with_capacity(fresh.report().declaration_identities.len());
    for identity in &fresh.report().declaration_identities {
        if matches!(
            identity.kind,
            DeclarationKind::Axiom
                | DeclarationKind::Theorem
                | DeclarationKind::Opaque
                | DeclarationKind::Quotient
        ) {
            return Err(TypeSliceReceiptError::TrustedFreshDeclaration {
                name: identity.name.clone(),
                kind: identity.kind,
            });
        }
        retained.push(TypeSliceRetainedReceipt {
            name: identity.name.clone(),
            kind: identity.kind.as_str().to_owned(),
            content_sha256: identity.content_sha256.clone(),
            dependency_sha256: identity.dependency_sha256.clone(),
        });
    }

    let mut raw_types = Vec::with_capacity(generalized.binders.len());
    for binder in &generalized.binders {
        let constant = source_kernel.const_(binder.source.name, binder.source.levels.clone());
        let ty = source_kernel
            .infer(constant)
            .map_err(|error| TypeSliceReceiptError::Identity(format!("source type: {error:?}")))?;
        raw_types.push(ty);
    }
    let mut abstractions = Vec::with_capacity(generalized.binders.len());
    for (binder_position, (binder, &raw_type)) in
        generalized.binders.iter().zip(&raw_types).enumerate()
    {
        let source_name = source_kernel.display_name(binder.source.name).to_string();
        let matches: Vec<_> = source_report
            .declaration_identities
            .iter()
            .filter(|identity| identity.name == source_name)
            .collect();
        if matches.len() != 1 {
            return Err(TypeSliceReceiptError::SourceDeclarationIdentity {
                name: source_name,
                observed: matches.len(),
            });
        }
        let source_content = canonical_declaration_sha256(source_kernel, binder.source.name)
            .map_err(TypeSliceReceiptError::Identity)?;
        if source_content != matches[0].content_sha256 {
            return Err(TypeSliceReceiptError::SourceContentIdentityMismatch { name: source_name });
        }
        let mut source_occurrences = expanded_occurrences(
            source_kernel,
            source_goal,
            binder.source.name,
            &binder.source.levels,
        )?;
        for &root in &raw_types {
            source_occurrences = source_occurrences
                .checked_add(expanded_occurrences(
                    source_kernel,
                    root,
                    binder.source.name,
                    &binder.source.levels,
                )?)
                .ok_or(TypeSliceReceiptError::OccurrenceOverflow)?;
        }
        abstractions.push(TypeSliceAbstractionReceipt {
            binder_position,
            source_name,
            source_content_sha256: source_content,
            universe_sha256: binder
                .source
                .levels
                .iter()
                .map(|&level| canonical_level_sha256(source_kernel, level))
                .collect(),
            instantiated_type_sha256: canonical_expression_sha256(source_kernel, raw_type)
                .map_err(TypeSliceReceiptError::Identity)?,
            source_occurrences,
        });
    }

    let transport_normalization = if let Some(normalization) = normalization {
        if normalization.rewritten_occurrences == 0
            || normalization.normalized_declarations.is_empty()
            || !normalization
                .normalized_declarations
                .windows(2)
                .all(|pair| pair[0] < pair[1])
        {
            return Err(TypeSliceReceiptError::NormalizationIdentity {
                reason: "normalization report is empty, duplicated, or unordered".to_owned(),
            });
        }
        let auto_param_name = source_kernel
            .environment()
            .iter()
            .find_map(|(&name, _)| {
                (source_kernel.display_name(name).to_string() == "autoParam").then_some(name)
            })
            .ok_or_else(|| TypeSliceReceiptError::NormalizationIdentity {
                reason: "source autoParam declaration is absent".to_owned(),
            })?;
        let auto_param_matches: Vec<_> = source_report
            .declaration_identities
            .iter()
            .filter(|identity| identity.name == "autoParam")
            .collect();
        if auto_param_matches.len() != 1 {
            return Err(TypeSliceReceiptError::NormalizationIdentity {
                reason: format!(
                    "source autoParam identity cardinality is {}",
                    auto_param_matches.len()
                ),
            });
        }
        let auto_param_source_content_sha256 =
            canonical_declaration_sha256(source_kernel, auto_param_name)
                .map_err(TypeSliceReceiptError::Identity)?;
        if auto_param_source_content_sha256 != auto_param_matches[0].content_sha256 {
            return Err(TypeSliceReceiptError::NormalizationIdentity {
                reason: "source autoParam content identity changed".to_owned(),
            });
        }
        let mut declarations = Vec::with_capacity(normalization.normalized_declarations.len());
        for name in &normalization.normalized_declarations {
            let source_name = source_kernel
                .environment()
                .iter()
                .find_map(|(&candidate, _)| {
                    (source_kernel.display_name(candidate).to_string() == *name)
                        .then_some(candidate)
                })
                .ok_or_else(|| TypeSliceReceiptError::NormalizationIdentity {
                    reason: format!("normalized source declaration {name} is absent"),
                })?;
            let source_matches: Vec<_> = source_report
                .declaration_identities
                .iter()
                .filter(|identity| identity.name == *name)
                .collect();
            let fresh_matches: Vec<_> = fresh
                .report()
                .declaration_identities
                .iter()
                .filter(|identity| identity.name == *name)
                .collect();
            if source_matches.len() != 1 || fresh_matches.len() != 1 {
                return Err(TypeSliceReceiptError::NormalizationIdentity {
                    reason: format!(
                        "normalized declaration {name} has source/fresh cardinality {}/{}",
                        source_matches.len(),
                        fresh_matches.len()
                    ),
                });
            }
            let source_content_sha256 = canonical_declaration_sha256(source_kernel, source_name)
                .map_err(TypeSliceReceiptError::Identity)?;
            if source_content_sha256 != source_matches[0].content_sha256
                || source_content_sha256 == fresh_matches[0].content_sha256
            {
                return Err(TypeSliceReceiptError::NormalizationIdentity {
                    reason: format!(
                        "normalized declaration identity did not change exactly: {name}"
                    ),
                });
            }
            declarations.push(TypeSliceNormalizedDeclarationReceipt {
                name: name.clone(),
                source_content_sha256,
                normalized_content_sha256: fresh_matches[0].content_sha256.clone(),
                normalized_dependency_sha256: fresh_matches[0].dependency_sha256.clone(),
            });
        }
        Some(TypeSliceTransportNormalizationReceipt {
            auto_param_source_content_sha256,
            rewritten_occurrences: normalization.rewritten_occurrences,
            declarations,
        })
    } else {
        None
    };

    let mut receipt = TypeSliceReceipt {
        schema_version: if transport_normalization.is_some() {
            NORMALIZED_TYPE_SLICE_RECEIPT_VERSION
        } else {
            TYPE_SLICE_RECEIPT_VERSION
        },
        policy_version: policy_version.to_owned(),
        source: TypeSliceSourceReceipt {
            stream_sha256: source_stream_sha256.to_owned(),
            format_version: source_report.format_version.clone(),
            lean_version: source_report.lean_version.clone(),
            lean_githash: source_report.lean_githash.clone(),
            exporter_version: source_report.exporter_version.clone(),
            declaration_identity_version: source_report.identity_version.to_owned(),
            target: source_target_name,
            target_content_sha256: source_target_matches[0].content_sha256.clone(),
            goal_sha256: source_goal_sha256,
        },
        sliced_goal_sha256,
        fresh_target_content_sha256: fresh_target_matches[0].content_sha256.clone(),
        abstractions,
        retained,
        transport_normalization,
        specialization_verified: true,
        receipt_sha256: String::new(),
    };
    let payload = serde_json::to_vec(&receipt.json_value(false))
        .map_err(|error| TypeSliceReceiptError::Identity(error.to_string()))?;
    receipt.receipt_sha256 = hex_sha256(&payload);
    Ok(receipt)
}

fn is_sha256(value: &str) -> bool {
    value.len() == 64
        && value
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
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

fn expanded_occurrences(
    kernel: &Kernel,
    root: ExprId,
    name: NameId,
    levels: &[axeyum_lean_kernel::LevelId],
) -> Result<u64, TypeSliceReceiptError> {
    fn count(
        kernel: &Kernel,
        expression: ExprId,
        name: NameId,
        levels: &[axeyum_lean_kernel::LevelId],
        memo: &mut HashMap<ExprId, u64>,
    ) -> Result<u64, TypeSliceReceiptError> {
        if let Some(&value) = memo.get(&expression) {
            return Ok(value);
        }
        let node = kernel.expr_node(expression);
        let mut total = u64::from(matches!(
            node,
            ExprNode::Const(observed_name, observed_levels)
                if *observed_name == name && observed_levels == levels
        ));
        for child in expression_children(node) {
            total = total
                .checked_add(count(kernel, child, name, levels, memo)?)
                .ok_or(TypeSliceReceiptError::OccurrenceOverflow)?;
        }
        memo.insert(expression, total);
        Ok(total)
    }

    count(kernel, root, name, levels, &mut HashMap::new())
}

fn expression_children(node: &ExprNode) -> Vec<ExprId> {
    match node {
        ExprNode::Proj(_, _, structure) => vec![*structure],
        ExprNode::App(function, argument) => vec![*function, *argument],
        ExprNode::Lam(_, ty, body, _) | ExprNode::Pi(_, ty, body, _) => vec![*ty, *body],
        ExprNode::Let(_, ty, value, body) => vec![*ty, *value, *body],
        ExprNode::BVar(_)
        | ExprNode::FVar(_)
        | ExprNode::Sort(_)
        | ExprNode::Const(_, _)
        | ExprNode::Lit(_) => Vec::new(),
    }
}
