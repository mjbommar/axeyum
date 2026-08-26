//! Checked theorem-rooted composition between independently owned kernels.
//!
//! This module implements ADR-0523's publication boundary. Compatibility only
//! authorizes an attempt; the target kernel independently checks every rebuilt
//! proof before the completed clone is published.

use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::fmt;
use std::fmt::Write as _;

use axeyum_lean_kernel::{
    Declaration, ExprId, ExprNode, Kernel, KernelError, LevelId, LevelNode, NameId, NameNode,
    ReducibilityHint, build_logic_prelude,
};
use serde_json::{Value, json};
use sha2::{Digest, Sha256};

use crate::{
    canonical_alpha_expression_sha256, canonical_declaration_sha256,
    canonical_kernel_type_shape_sha256,
};

/// Version of the checked theorem-composition receipt and compatibility policy.
pub const CHECKED_THEOREM_COMPOSITION_VERSION: &str = "axeyum.checked-theorem-composition.v5";

/// Version of theorem composition with explicit target-owned theorem leaves.
pub const CHECKED_TARGET_LEAF_THEOREM_COMPOSITION_VERSION: &str =
    "axeyum.checked-theorem-composition.target-leaves.v1";

/// Declaration-exact Lean 4.30 `Acc` package accepted by the recursive
/// singleton gate. Names alone never authorize recursive reconstruction.
const OFFICIAL_LEAN_4_30_ACC_PACKAGE_SHA256: [&str; 3] = [
    "ae8b799311c1ef25f167d7413eb10abf55df398053cf994f953bd31624f96e27",
    "73c42b8287c3b2b680731deb89003732efda90b571c0dd737a81cbcf2ef024c2",
    "67cc978e963fa24e78a117380175be35753a051986230e1c5f2fd2b3a2df85ac",
];

/// The checked relation that authorized reuse of one target declaration.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ReusedTypeCompatibility {
    /// Canonical kernel-relevant type shapes are identical.
    KernelTypeShape,
    /// The rebuilt source type is definitionally equal to the target type.
    TranslatedDefinitionalEquality,
}

impl ReusedTypeCompatibility {
    /// Stable receipt spelling for this relation.
    #[must_use]
    pub fn as_str(self) -> &'static str {
        match self {
            Self::KernelTypeShape => "kernel-type-shape",
            Self::TranslatedDefinitionalEquality => "translated-definitional-equality",
        }
    }
}

/// One source declaration reused from the target environment.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ReusedDeclarationReceipt {
    /// Complete rendered declaration name.
    pub name: String,
    /// Exact source declaration identity.
    pub source_declaration_sha256: String,
    /// Exact target declaration identity before composition.
    pub target_declaration_sha256: String,
    /// Kernel-relevant source type-shape identity.
    pub source_type_shape_sha256: String,
    /// Kernel-relevant target type-shape identity.
    pub target_type_shape_sha256: String,
    /// Checked compatibility relation that authorized this reuse attempt.
    pub compatibility: ReusedTypeCompatibility,
}

/// Checked compatibility between two closed proposition expressions.
///
/// Unlike [`ReusedDeclarationReceipt`], this compares the propositions
/// themselves rather than the declarations' outer types. It is the diagnostic
/// boundary needed for a proof-free `definition : Prop := statement`, whose
/// declaration type alone is merely `Prop`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PropositionCompatibilityReceipt {
    /// Alpha-stable identity of the source proposition.
    pub source_proposition_sha256: String,
    /// Alpha-stable identity of the target proposition.
    pub target_proposition_sha256: String,
    /// Kernel-relevant source proposition shape.
    pub source_shape_sha256: String,
    /// Kernel-relevant target proposition shape.
    pub target_shape_sha256: String,
    /// Checked cross-kernel relation.
    pub compatibility: ReusedTypeCompatibility,
}

/// One checked theorem newly admitted to the completed target.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AddedTheoremReceipt {
    /// Complete rendered theorem name.
    pub name: String,
    /// Exact declaration identity in the source kernel.
    pub source_declaration_sha256: String,
    /// Exact declaration identity after independent target admission.
    pub target_declaration_sha256: String,
    /// Kernel-derived assumptions reached by the admitted theorem.
    pub axiom_footprint: Vec<String>,
}

/// One missing definition independently admitted to the target clone.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AddedDefinitionReceipt {
    /// Complete declaration name.
    pub name: String,
    /// Exact source definition identity.
    pub source_declaration_sha256: String,
    /// Exact independently admitted target identity.
    pub target_declaration_sha256: String,
    /// Stable spelling of the preserved reducibility hint.
    pub reducibility: String,
}

/// One atomically reconstructed singleton inductive package.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AddedSingletonInductiveReceipt {
    /// Complete family name.
    pub family: String,
    /// Complete constructor names in checked source order.
    pub constructors: Vec<String>,
    /// Complete generated recursor name.
    pub recursor: String,
    /// Exact source identities for family, constructors, and recursor.
    pub source_declaration_sha256: BTreeMap<String, String>,
    /// Exact independently reconstructed target identities.
    pub target_declaration_sha256: BTreeMap<String, String>,
}

/// Deterministic receipt for one completed theorem-rooted composition.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CheckedTheoremCompositionReceipt {
    /// Compatibility, translation, and receipt schema.
    pub schema_version: String,
    /// Explicit roots requested by the caller, in caller order.
    pub roots: Vec<String>,
    /// Explicit compatible, axiom-free target theorems whose source proofs were
    /// not traversed. Empty for the original V5 operation.
    pub target_theorem_leaves: Vec<String>,
    /// Root-selected source closure in dependency order.
    pub source_closure: Vec<String>,
    /// Exact target environment identity before composition.
    pub target_environment_sha256_before: String,
    /// Existing target declarations reused after type-shape validation.
    pub reused_declarations: Vec<ReusedDeclarationReceipt>,
    /// Missing source theorems independently admitted to the target clone.
    pub added_theorems: Vec<AddedTheoremReceipt>,
    /// Missing source definitions independently admitted in dependency order.
    pub added_definitions: Vec<AddedDefinitionReceipt>,
    /// Missing singleton inductives atomically reconstructed before theorem admission.
    pub added_singleton_inductives: Vec<AddedSingletonInductiveReceipt>,
    /// Exact target environment identity after composition.
    pub target_environment_sha256_after: String,
    /// Canonical digest of every preceding receipt field.
    pub receipt_sha256: String,
}

impl CheckedTheoremCompositionReceipt {
    /// Recompute the canonical receipt digest.
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
            "roots": self.roots,
            "source_closure": self.source_closure,
            "target_environment_sha256_before": self.target_environment_sha256_before,
            "reused_declarations": self.reused_declarations.iter().map(|row| json!({
                "name": row.name,
                "source_declaration_sha256": row.source_declaration_sha256,
                "target_declaration_sha256": row.target_declaration_sha256,
                "source_type_shape_sha256": row.source_type_shape_sha256,
                "target_type_shape_sha256": row.target_type_shape_sha256,
                "compatibility": row.compatibility.as_str(),
            })).collect::<Vec<_>>(),
            "added_theorems": self.added_theorems.iter().map(|row| json!({
                "name": row.name,
                "source_declaration_sha256": row.source_declaration_sha256,
                "target_declaration_sha256": row.target_declaration_sha256,
                "axiom_footprint": row.axiom_footprint,
            })).collect::<Vec<_>>(),
            "added_definitions": self.added_definitions.iter().map(|row| json!({
                "name": row.name,
                "source_declaration_sha256": row.source_declaration_sha256,
                "target_declaration_sha256": row.target_declaration_sha256,
                "reducibility": row.reducibility,
            })).collect::<Vec<_>>(),
            "added_singleton_inductives": self.added_singleton_inductives.iter().map(|row| json!({
                "family": row.family,
                "constructors": row.constructors,
                "recursor": row.recursor,
                "source_declaration_sha256": row.source_declaration_sha256,
                "target_declaration_sha256": row.target_declaration_sha256,
            })).collect::<Vec<_>>(),
            "target_environment_sha256_after": self.target_environment_sha256_after,
        });
        if !self.target_theorem_leaves.is_empty()
            && let Some(object) = value.as_object_mut()
        {
            object.insert(
                "target_theorem_leaves".to_owned(),
                json!(self.target_theorem_leaves),
            );
        }
        if include_digest && let Some(object) = value.as_object_mut() {
            object.insert(
                "receipt_sha256".to_owned(),
                Value::String(self.receipt_sha256.clone()),
            );
        }
        value
    }
}

/// An owned target environment published only after the complete slice passes.
#[derive(Debug)]
pub struct CompletedTheoremComposition {
    kernel: Kernel,
    receipt: CheckedTheoremCompositionReceipt,
}

impl CompletedTheoremComposition {
    /// Borrow the independently checked completed target.
    #[must_use]
    pub fn kernel(&self) -> &Kernel {
        &self.kernel
    }

    /// Borrow the recomputable composition receipt.
    #[must_use]
    pub fn receipt(&self) -> &CheckedTheoremCompositionReceipt {
        &self.receipt
    }

    /// Transfer ownership of the checked target and its matching receipt.
    #[must_use]
    pub fn into_parts(self) -> (Kernel, CheckedTheoremCompositionReceipt) {
        (self.kernel, self.receipt)
    }
}

/// A fail-closed theorem-composition decline.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CheckedTheoremCompositionError {
    /// At least one explicit root is required.
    EmptyRoots,
    /// Root names must be unique.
    DuplicateRoot(String),
    /// A requested source root does not exist.
    MissingRoot(String),
    /// A named compatibility check has no same-name target declaration.
    MissingTarget(String),
    /// Every requested root must already be a checked theorem.
    RootIsNotTheorem(String),
    /// The kernel could not derive a closed dependency order.
    Closure(String),
    /// A same-name target declaration has a different kernel type shape.
    TypeShapeMismatch {
        /// Conflicting complete declaration name.
        name: String,
        /// Source type-shape digest.
        source_sha256: String,
        /// Target type-shape digest.
        target_sha256: String,
    },
    /// One expression supplied to proposition compatibility does not infer to
    /// `Prop` in its owning kernel.
    ExpressionNotProposition {
        /// Stable side name.
        side: &'static str,
    },
    /// The current schema admits only missing definitions, checked theorems,
    /// complete non-recursive singleton inductive packages, and the exact
    /// canonical native `Acc` package.
    UnsupportedMissingDeclaration {
        /// Complete declaration name.
        name: String,
        /// Source declaration variant.
        kind: String,
    },
    /// A checked declaration unexpectedly contained a free variable.
    FreeVariable,
    /// The independent target gate rejected a rebuilt theorem.
    AdmissionRejected {
        /// The theorem being admitted.
        name: String,
        /// Typed kernel error rendered without exposing target handles.
        error: String,
    },
    /// An exact recursive package regenerated successfully but did not match
    /// the canonical source family, constructor, or recursor identity.
    ReconstructedInductiveMismatch {
        /// Complete declaration name whose checked content drifted.
        name: String,
        /// Exact canonical source identity.
        source_sha256: String,
        /// Exact canonical regenerated-target identity.
        target_sha256: String,
    },
    /// The requested closure would add no declaration.
    NoAdditions,
    /// Canonical identity derivation failed.
    Identity(String),
    /// A supplied receipt or completed environment did not reproduce.
    ReceiptMismatch,
    /// The target-leaf operation requires at least one explicit theorem leaf.
    EmptyTargetTheoremLeaves,
    /// One explicit target theorem leaf is invalid.
    InvalidTargetTheoremLeaf {
        /// Complete rendered declaration name.
        name: String,
        /// Stable reason for rejection.
        reason: &'static str,
    },
    /// A target theorem leaf reaches one or more assumptions.
    TargetTheoremLeafAxiomFootprint {
        /// Complete rendered theorem name.
        name: String,
        /// Kernel-derived assumptions reached by the target theorem.
        footprint: Vec<String>,
    },
}

impl fmt::Display for CheckedTheoremCompositionError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{self:?}")
    }
}

impl std::error::Error for CheckedTheoremCompositionError {}

/// Compose a theorem-rooted source slice into an owned clone of `target`.
///
/// `target` is never mutated. The function validates all reused declarations
/// before cloning, admits every supported missing declaration into the private
/// clone, and returns the clone only after the complete slice succeeds.
///
/// # Errors
///
/// Declines on invalid roots, incompatible reused types, unsupported or partial
/// missing declaration packages, non-closed terms, identity failures, or a
/// trusted-gate rejection. Complete non-recursive singleton inductives and the
/// exact canonical native `Acc` package are reconstructed atomically before
/// missing theorem admission. No error publishes a target kernel.
pub fn compose_checked_theorem_slice(
    source: &Kernel,
    target: &Kernel,
    roots: &[&str],
) -> Result<CompletedTheoremComposition, CheckedTheoremCompositionError> {
    let selected = select_closure(source, roots)?;
    compose_selected_theorem_slice(
        source,
        target,
        roots,
        &[],
        &selected,
        CHECKED_THEOREM_COMPOSITION_VERSION,
    )
}

/// Compose a theorem-rooted slice while treating explicit compatible,
/// axiom-free target theorems as dependency leaves.
///
/// Each leaf must be a unique checked theorem in both kernels, have an empty
/// target footprint, be reachable from the requested source roots, and pass
/// the same target type-compatibility check as ordinary reuse. Its source type
/// dependencies remain in the selected closure, but its unrelated source proof
/// dependencies do not. The target is borrowed immutably and publication stays
/// private-clone atomic.
///
/// # Errors
///
/// Returns the ordinary composition declines plus a typed leaf error for an
/// empty, duplicate, missing, non-theorem, assumption-bearing, incompatible,
/// or unreachable target leaf.
pub fn compose_checked_theorem_slice_with_target_leaves(
    source: &Kernel,
    target: &Kernel,
    roots: &[&str],
    target_theorem_leaves: &[&str],
) -> Result<CompletedTheoremComposition, CheckedTheoremCompositionError> {
    if target_theorem_leaves.is_empty() {
        return Err(CheckedTheoremCompositionError::EmptyTargetTheoremLeaves);
    }
    let source_names = declaration_names(source);
    let target_names = declaration_names(target);
    let mut unique = BTreeSet::new();
    let mut leaf_ids = Vec::with_capacity(target_theorem_leaves.len());
    for &leaf in target_theorem_leaves {
        if !unique.insert(leaf) {
            return Err(CheckedTheoremCompositionError::InvalidTargetTheoremLeaf {
                name: leaf.to_owned(),
                reason: "duplicate",
            });
        }
        let Some(&source_leaf) = source_names.get(leaf) else {
            return Err(CheckedTheoremCompositionError::InvalidTargetTheoremLeaf {
                name: leaf.to_owned(),
                reason: "missing from source",
            });
        };
        if !matches!(
            source.environment().get(source_leaf),
            Some(Declaration::Theorem { .. })
        ) {
            return Err(CheckedTheoremCompositionError::InvalidTargetTheoremLeaf {
                name: leaf.to_owned(),
                reason: "source declaration is not a theorem",
            });
        }
        let Some(&target_leaf) = target_names.get(leaf) else {
            return Err(CheckedTheoremCompositionError::InvalidTargetTheoremLeaf {
                name: leaf.to_owned(),
                reason: "missing from target",
            });
        };
        if !matches!(
            target.environment().get(target_leaf),
            Some(Declaration::Theorem { .. })
        ) {
            return Err(CheckedTheoremCompositionError::InvalidTargetTheoremLeaf {
                name: leaf.to_owned(),
                reason: "target declaration is not a theorem",
            });
        }
        let footprint = target
            .axiom_footprint(target_leaf)
            .iter()
            .map(|&name| target.display_name(name).to_string())
            .collect::<Vec<_>>();
        if !footprint.is_empty() {
            return Err(
                CheckedTheoremCompositionError::TargetTheoremLeafAxiomFootprint {
                    name: leaf.to_owned(),
                    footprint,
                },
            );
        }
        leaf_ids.push(source_leaf);
    }
    let root_ids = select_root_ids(source, roots)?;
    let selected = source
        .root_declaration_closure_with_theorem_leaves(&root_ids, &leaf_ids)
        .map_err(|error| CheckedTheoremCompositionError::Closure(format!("{error:?}")))?;
    compose_selected_theorem_slice(
        source,
        target,
        roots,
        target_theorem_leaves,
        &selected,
        CHECKED_TARGET_LEAF_THEOREM_COMPOSITION_VERSION,
    )
}

fn compose_selected_theorem_slice(
    source: &Kernel,
    target: &Kernel,
    roots: &[&str],
    target_theorem_leaves: &[&str],
    selected: &[NameId],
    schema_version: &str,
) -> Result<CompletedTheoremComposition, CheckedTheoremCompositionError> {
    let target_names = declaration_names(target);
    let reused = validate_reused(source, target, selected, &target_names)?;
    let missing: Vec<NameId> = selected
        .iter()
        .copied()
        .filter(|name| !target_names.contains_key(&source.display_name(*name).to_string()))
        .collect();
    if missing.is_empty() {
        return Err(CheckedTheoremCompositionError::NoAdditions);
    }
    let singleton_packages = validate_missing_declarations(source, &missing)?;

    let before = environment_sha256(target)?;
    let mut staged = target.clone();
    let admitted = admit_missing_declarations_in_dependency_order(
        source,
        &mut staged,
        &missing,
        &singleton_packages,
    )?;
    let after = environment_sha256(&staged)?;
    let mut receipt = CheckedTheoremCompositionReceipt {
        schema_version: schema_version.to_owned(),
        roots: roots.iter().map(|root| (*root).to_owned()).collect(),
        target_theorem_leaves: target_theorem_leaves
            .iter()
            .map(|leaf| (*leaf).to_owned())
            .collect(),
        source_closure: selected
            .iter()
            .map(|name| source.display_name(*name).to_string())
            .collect(),
        target_environment_sha256_before: before,
        reused_declarations: reused,
        added_theorems: admitted.theorems,
        added_definitions: admitted.definitions,
        added_singleton_inductives: admitted.singleton_inductives,
        target_environment_sha256_after: after,
        receipt_sha256: String::new(),
    };
    let payload = serde_json::to_vec(&receipt.json_value(false))
        .map_err(|error| CheckedTheoremCompositionError::Identity(error.to_string()))?;
    receipt.receipt_sha256 = hex_sha256(&payload);
    Ok(CompletedTheoremComposition {
        kernel: staged,
        receipt,
    })
}

/// Re-run a composition and require the receipt and completed identity to match.
///
/// # Errors
///
/// Returns the original composition decline or [`CheckedTheoremCompositionError::ReceiptMismatch`]
/// when the supplied receipt or completed environment does not reproduce.
pub fn verify_checked_theorem_composition(
    source: &Kernel,
    target: &Kernel,
    completed: &Kernel,
    receipt: &CheckedTheoremCompositionReceipt,
) -> Result<(), CheckedTheoremCompositionError> {
    if !receipt.has_valid_digest() {
        return Err(CheckedTheoremCompositionError::ReceiptMismatch);
    }
    let roots: Vec<&str> = receipt.roots.iter().map(String::as_str).collect();
    let reproduced = compose_checked_theorem_slice(source, target, &roots)?;
    if reproduced.receipt != *receipt
        || environment_sha256(completed)? != receipt.target_environment_sha256_after
        || environment_sha256(reproduced.kernel())? != receipt.target_environment_sha256_after
    {
        return Err(CheckedTheoremCompositionError::ReceiptMismatch);
    }
    Ok(())
}

/// Replay target-leaf theorem composition and require the receipt and completed
/// environment identity to match exactly.
///
/// # Errors
///
/// Returns the original target-leaf composition decline or `ReceiptMismatch`
/// when the schema, digest, receipt, or completed environment does not
/// reproduce.
pub fn verify_checked_theorem_composition_with_target_leaves(
    source: &Kernel,
    target: &Kernel,
    completed: &Kernel,
    receipt: &CheckedTheoremCompositionReceipt,
) -> Result<(), CheckedTheoremCompositionError> {
    if receipt.schema_version != CHECKED_TARGET_LEAF_THEOREM_COMPOSITION_VERSION
        || !receipt.has_valid_digest()
    {
        return Err(CheckedTheoremCompositionError::ReceiptMismatch);
    }
    let roots = receipt.roots.iter().map(String::as_str).collect::<Vec<_>>();
    let leaves = receipt
        .target_theorem_leaves
        .iter()
        .map(String::as_str)
        .collect::<Vec<_>>();
    let reproduced =
        compose_checked_theorem_slice_with_target_leaves(source, target, &roots, &leaves)?;
    if reproduced.receipt != *receipt
        || environment_sha256(completed)? != receipt.target_environment_sha256_after
        || environment_sha256(reproduced.kernel())? != receipt.target_environment_sha256_after
    {
        return Err(CheckedTheoremCompositionError::ReceiptMismatch);
    }
    Ok(())
}

/// Check the exact reuse relation for one same-name declaration without
/// selecting a proof closure or publishing any declaration.
///
/// This is a diagnostic for the same compatibility boundary used by
/// [`compose_checked_theorem_slice`]. A successful receipt authorizes only a
/// later target-kernel reconstruction attempt; it is not proof or admission
/// evidence by itself.
///
/// # Errors
///
/// Returns a missing-name, type-shape, translation, or identity error. Neither
/// input kernel is mutated.
pub fn checked_reused_declaration_compatibility(
    source: &Kernel,
    target: &Kernel,
    name: &str,
) -> Result<ReusedDeclarationReceipt, CheckedTheoremCompositionError> {
    let source_names = declaration_names(source);
    let source_name = source_names
        .get(name)
        .copied()
        .ok_or_else(|| CheckedTheoremCompositionError::MissingRoot(name.to_owned()))?;
    let target_names = declaration_names(target);
    if !target_names.contains_key(name) {
        return Err(CheckedTheoremCompositionError::MissingTarget(
            name.to_owned(),
        ));
    }
    validate_reused(source, target, &[source_name], &target_names)?
        .pop()
        .ok_or_else(|| {
            CheckedTheoremCompositionError::Identity(
                "named compatibility check produced no receipt".to_owned(),
            )
        })
}

/// Compare two closed propositions across independently owned kernels.
///
/// The source expression is translated by exact rendered declaration names
/// into a private clone of the target, independently inferred there, and
/// compared by target-kernel definitional equality. This reads no theorem proof
/// value and mutates neither input. A successful receipt authorizes only a
/// later proof/reuse attempt; it is not fact or admission evidence.
///
/// # Errors
///
/// Returns a typed composition diagnostic if either expression is not a closed
/// proposition, translation fails, or the translated propositions differ.
pub fn checked_proposition_compatibility(
    source: &Kernel,
    source_proposition: ExprId,
    target: &Kernel,
    target_proposition: ExprId,
) -> Result<PropositionCompatibilityReceipt, CheckedTheoremCompositionError> {
    let mut source_check = source.clone();
    let source_type = source_check
        .infer(source_proposition)
        .map_err(|_| CheckedTheoremCompositionError::ExpressionNotProposition { side: "source" })?;
    let source_zero = source_check.level_zero();
    let source_prop = source_check.sort(source_zero);
    if !source_check.def_eq(source_type, source_prop) {
        return Err(CheckedTheoremCompositionError::ExpressionNotProposition { side: "source" });
    }

    let mut target_check = target.clone();
    let target_type = target_check
        .infer(target_proposition)
        .map_err(|_| CheckedTheoremCompositionError::ExpressionNotProposition { side: "target" })?;
    let target_zero = target_check.level_zero();
    let target_prop = target_check.sort(target_zero);
    if !target_check.def_eq(target_type, target_prop) {
        return Err(CheckedTheoremCompositionError::ExpressionNotProposition { side: "target" });
    }

    let mut translated_target = target.clone();
    let mut translator = ExpressionTranslator::new(source, &mut translated_target);
    let translated = translator.expr(source_proposition)?;
    if translator.target.infer(translated).is_err()
        || !translator.target.def_eq(translated, target_proposition)
    {
        return Err(CheckedTheoremCompositionError::TypeShapeMismatch {
            name: "<proposition>".to_owned(),
            source_sha256: type_shape(source, source_proposition)?,
            target_sha256: type_shape(target, target_proposition)?,
        });
    }
    Ok(PropositionCompatibilityReceipt {
        source_proposition_sha256: canonical_alpha_expression_sha256(source, source_proposition)
            .map_err(CheckedTheoremCompositionError::Identity)?,
        target_proposition_sha256: canonical_alpha_expression_sha256(target, target_proposition)
            .map_err(CheckedTheoremCompositionError::Identity)?,
        source_shape_sha256: type_shape(source, source_proposition)?,
        target_shape_sha256: type_shape(target, target_proposition)?,
        compatibility: ReusedTypeCompatibility::TranslatedDefinitionalEquality,
    })
}

fn select_closure(
    source: &Kernel,
    roots: &[&str],
) -> Result<Vec<NameId>, CheckedTheoremCompositionError> {
    let root_ids = select_root_ids(source, roots)?;
    source
        .root_declaration_closure(&root_ids)
        .map_err(|error| CheckedTheoremCompositionError::Closure(format!("{error:?}")))
}

fn select_root_ids(
    source: &Kernel,
    roots: &[&str],
) -> Result<Vec<NameId>, CheckedTheoremCompositionError> {
    if roots.is_empty() {
        return Err(CheckedTheoremCompositionError::EmptyRoots);
    }
    let names = declaration_names(source);
    let mut unique = BTreeSet::new();
    let mut root_ids = Vec::with_capacity(roots.len());
    for &root in roots {
        if !unique.insert(root) {
            return Err(CheckedTheoremCompositionError::DuplicateRoot(
                root.to_owned(),
            ));
        }
        let id = names
            .get(root)
            .copied()
            .ok_or_else(|| CheckedTheoremCompositionError::MissingRoot(root.to_owned()))?;
        if !matches!(
            source.environment().get(id),
            Some(Declaration::Theorem { .. })
        ) {
            return Err(CheckedTheoremCompositionError::RootIsNotTheorem(
                root.to_owned(),
            ));
        }
        root_ids.push(id);
    }
    Ok(root_ids)
}

fn validate_reused(
    source: &Kernel,
    target: &Kernel,
    selected: &[NameId],
    target_names: &BTreeMap<String, NameId>,
) -> Result<Vec<ReusedDeclarationReceipt>, CheckedTheoremCompositionError> {
    let mut reused = Vec::new();
    let mut compatibility_target = target.clone();
    let mut compatibility_translator = ExpressionTranslator::new(source, &mut compatibility_target);
    for &source_name in selected {
        let rendered = source.display_name(source_name).to_string();
        let Some(&target_name) = target_names.get(&rendered) else {
            continue;
        };
        let source_type = source
            .environment()
            .get(source_name)
            .ok_or_else(|| {
                CheckedTheoremCompositionError::Identity(
                    "selected source declaration disappeared".to_owned(),
                )
            })?
            .ty();
        let target_type = target
            .environment()
            .get(target_name)
            .ok_or_else(|| {
                CheckedTheoremCompositionError::Identity(
                    "mapped target declaration disappeared".to_owned(),
                )
            })?
            .ty();
        let source_shape = type_shape(source, source_type)?;
        let target_shape = type_shape(target, target_type)?;
        let compatibility = if source_shape == target_shape {
            ReusedTypeCompatibility::KernelTypeShape
        } else if translated_type_is_definitionally_equal(
            &mut compatibility_translator,
            source_type,
            target_type,
        )? {
            ReusedTypeCompatibility::TranslatedDefinitionalEquality
        } else {
            return Err(CheckedTheoremCompositionError::TypeShapeMismatch {
                name: rendered,
                source_sha256: source_shape,
                target_sha256: target_shape,
            });
        };
        reused.push(ReusedDeclarationReceipt {
            name: rendered,
            source_declaration_sha256: declaration_sha256(source, source_name)?,
            target_declaration_sha256: declaration_sha256(target, target_name)?,
            source_type_shape_sha256: source_shape,
            target_type_shape_sha256: target_shape,
            compatibility,
        });
    }
    Ok(reused)
}

fn translated_type_is_definitionally_equal(
    translator: &mut ExpressionTranslator<'_>,
    source_type: ExprId,
    target_type: ExprId,
) -> Result<bool, CheckedTheoremCompositionError> {
    let translated = translator.expr(source_type)?;
    let Ok(inferred) = translator.target.infer(translated) else {
        return Ok(false);
    };
    let inferred = translator.target.whnf(inferred);
    if !matches!(translator.target.expr_node(inferred), ExprNode::Sort(_)) {
        return Ok(false);
    }
    Ok(translator.target.def_eq(translated, target_type))
}

#[derive(Debug)]
struct SingletonInductivePackage {
    family: NameId,
    constructors: Vec<NameId>,
    recursor: NameId,
    require_exact_reconstruction: bool,
}

fn validate_missing_declarations(
    source: &Kernel,
    missing: &[NameId],
) -> Result<Vec<SingletonInductivePackage>, CheckedTheoremCompositionError> {
    let missing_set = missing.iter().copied().collect::<BTreeSet<_>>();
    let names = declaration_names(source);
    let mut package_members = BTreeSet::new();
    let mut packages = Vec::new();
    for &family in missing {
        if !matches!(
            source.environment().get(family),
            Some(Declaration::Inductive { .. })
        ) {
            continue;
        }
        let package = validate_singleton_inductive(source, family, &missing_set, &names)?;
        package_members.insert(package.family);
        package_members.extend(package.constructors.iter().copied());
        package_members.insert(package.recursor);
        packages.push(package);
    }
    for &name in missing {
        let declaration = source.environment().get(name).ok_or_else(|| {
            CheckedTheoremCompositionError::Identity(
                "selected source declaration disappeared".to_owned(),
            )
        })?;
        if !matches!(
            declaration,
            Declaration::Definition { .. } | Declaration::Theorem { .. }
        ) && !package_members.contains(&name)
        {
            return Err(
                CheckedTheoremCompositionError::UnsupportedMissingDeclaration {
                    name: source.display_name(name).to_string(),
                    kind: declaration_kind(declaration).to_owned(),
                },
            );
        }
    }
    Ok(packages)
}

fn validate_singleton_inductive(
    source: &Kernel,
    family: NameId,
    missing: &BTreeSet<NameId>,
    names: &BTreeMap<String, NameId>,
) -> Result<SingletonInductivePackage, CheckedTheoremCompositionError> {
    let Some(Declaration::Inductive {
        uparams,
        num_params,
        num_indices,
        is_recursive,
        ctor_names,
        ..
    }) = source.environment().get(family)
    else {
        unreachable!("caller selects only inductive declarations")
    };
    let rendered = source.display_name(family).to_string();
    let recursor_rendered = format!("{rendered}.rec");
    let Some(&recursor) = names.get(&recursor_rendered) else {
        return Err(
            CheckedTheoremCompositionError::UnsupportedMissingDeclaration {
                name: rendered,
                kind: "singleton-inductive-without-recursor".to_owned(),
            },
        );
    };
    let Some(Declaration::Recursor {
        num_motives,
        num_params: recursor_num_params,
        num_indices: recursor_num_indices,
        rec_rules,
        ..
    }) = source.environment().get(recursor)
    else {
        return Err(
            CheckedTheoremCompositionError::UnsupportedMissingDeclaration {
                name: recursor_rendered,
                kind: "invalid-recursor".to_owned(),
            },
        );
    };
    let recursor_constructors = rec_rules
        .iter()
        .map(|rule| rule.ctor_name)
        .collect::<Vec<_>>();
    let complete = *num_motives == 1
        && recursor_num_params == num_params
        && recursor_num_indices == num_indices
        && recursor_constructors == *ctor_names
        && missing.contains(&recursor)
        && ctor_names.iter().all(|name| missing.contains(name));
    if !complete {
        return Err(
            CheckedTheoremCompositionError::UnsupportedMissingDeclaration {
                name: rendered,
                kind: "non-singleton-or-partial-inductive-package".to_owned(),
            },
        );
    }
    for (index, &constructor) in ctor_names.iter().enumerate() {
        let Some(Declaration::Constructor {
            uparams: ctor_uparams,
            inductive,
            idx,
            ..
        }) = source.environment().get(constructor)
        else {
            return Err(
                CheckedTheoremCompositionError::UnsupportedMissingDeclaration {
                    name: source.display_name(constructor).to_string(),
                    kind: "invalid-constructor".to_owned(),
                },
            );
        };
        if ctor_uparams != uparams || *inductive != family || usize::from(*idx) != index {
            return Err(
                CheckedTheoremCompositionError::UnsupportedMissingDeclaration {
                    name: source.display_name(constructor).to_string(),
                    kind: "inconsistent-singleton-constructor".to_owned(),
                },
            );
        }
    }
    let require_exact_reconstruction = if *is_recursive {
        if !is_canonical_native_acc_package(source, family, ctor_names, recursor)? {
            return Err(
                CheckedTheoremCompositionError::UnsupportedMissingDeclaration {
                    name: rendered,
                    kind: "recursive-inductive".to_owned(),
                },
            );
        }
        true
    } else {
        false
    };
    Ok(SingletonInductivePackage {
        family,
        constructors: ctor_names.clone(),
        recursor,
        require_exact_reconstruction,
    })
}

/// The recursive composition boundary is deliberately a declaration-exact
/// allow-list, not a structural class. A source can call an arbitrary family
/// `Acc`; only the package produced by Axeyum's checked logic prelude receives
/// this authority. The target still reconstructs and independently checks the
/// package below.
fn is_canonical_native_acc_package(
    source: &Kernel,
    family: NameId,
    constructors: &[NameId],
    recursor: NameId,
) -> Result<bool, CheckedTheoremCompositionError> {
    if source.display_name(family).to_string() != "Acc"
        || constructors.len() != 1
        || source.display_name(constructors[0]).to_string() != "Acc.intro"
        || source.display_name(recursor).to_string() != "Acc.rec"
    {
        return Ok(false);
    }

    let source_identity = [family, constructors[0], recursor]
        .map(|name| declaration_sha256(source, name))
        .into_iter()
        .collect::<Result<Vec<_>, _>>()?;
    if acc_package_identity_is_authorized(&source_identity) {
        return Ok(true);
    }

    let mut reference = Kernel::new();
    build_logic_prelude(&mut reference).map_err(|error| {
        CheckedTheoremCompositionError::Identity(format!(
            "canonical native Acc reference failed to build: {error:?}"
        ))
    })?;
    let reference_names = declaration_names(&reference);
    let mut reference_identity = Vec::with_capacity(3);
    for rendered in ["Acc", "Acc.intro", "Acc.rec"] {
        let Some(&reference_name) = reference_names.get(rendered) else {
            return Err(CheckedTheoremCompositionError::Identity(format!(
                "canonical native Acc reference is missing {rendered}"
            )));
        };
        reference_identity.push(declaration_sha256(&reference, reference_name)?);
    }
    Ok(source_identity == reference_identity)
}

fn acc_package_identity_is_authorized(identity: &[String]) -> bool {
    identity
        == OFFICIAL_LEAN_4_30_ACC_PACKAGE_SHA256
            .iter()
            .map(|digest| (*digest).to_owned())
            .collect::<Vec<_>>()
}

fn admit_one_singleton_inductive(
    source: &Kernel,
    translator: &mut ExpressionTranslator<'_>,
    package: &SingletonInductivePackage,
) -> Result<AddedSingletonInductiveReceipt, CheckedTheoremCompositionError> {
    let Some(Declaration::Inductive {
        name,
        uparams,
        ty,
        num_params,
        ..
    }) = source.environment().get(package.family).cloned()
    else {
        return Err(CheckedTheoremCompositionError::Identity(
            "validated singleton family disappeared".to_owned(),
        ));
    };
    let target_family = translator.name(name);
    let target_uparams = uparams
        .into_iter()
        .map(|name| translator.name(name))
        .collect::<Vec<_>>();
    let target_type = translator.expr(ty)?;
    let mut target_constructors = Vec::with_capacity(package.constructors.len());
    for &constructor in &package.constructors {
        let Some(Declaration::Constructor { name, ty, .. }) =
            source.environment().get(constructor).cloned()
        else {
            return Err(CheckedTheoremCompositionError::Identity(
                "validated singleton constructor disappeared".to_owned(),
            ));
        };
        let name = translator.name(name);
        let ty = translator.expr(ty)?;
        target_constructors.push((name, ty));
    }
    translator
        .target
        .add_inductive(
            target_family,
            &target_uparams,
            usize::from(num_params),
            target_type,
            &target_constructors,
        )
        .map_err(|error| CheckedTheoremCompositionError::AdmissionRejected {
            name: source.display_name(package.family).to_string(),
            error: explain_admission_error(translator.target, &error),
        })?;

    let family = source.display_name(package.family).to_string();
    let constructors = package
        .constructors
        .iter()
        .map(|name| source.display_name(*name).to_string())
        .collect::<Vec<_>>();
    let recursor = source.display_name(package.recursor).to_string();
    let package_declarations = std::iter::once((family.clone(), package.family))
        .chain(
            constructors
                .iter()
                .cloned()
                .zip(package.constructors.iter().copied()),
        )
        .chain(std::iter::once((recursor.clone(), package.recursor)))
        .collect::<Vec<_>>();
    let target_names = declaration_names(translator.target);
    let mut source_digests = BTreeMap::new();
    let mut target_digests = BTreeMap::new();
    for (rendered, source_name) in package_declarations {
        let target_name = target_names.get(&rendered).copied().ok_or_else(|| {
            CheckedTheoremCompositionError::Identity(format!(
                "reconstructed singleton declaration is absent: {rendered}"
            ))
        })?;
        let source_digest = declaration_sha256(source, source_name)?;
        let target_digest = declaration_sha256(translator.target, target_name)?;
        if package.require_exact_reconstruction && source_digest != target_digest {
            return Err(
                CheckedTheoremCompositionError::ReconstructedInductiveMismatch {
                    name: rendered,
                    source_sha256: source_digest,
                    target_sha256: target_digest,
                },
            );
        }
        source_digests.insert(rendered.clone(), source_digest);
        target_digests.insert(rendered, target_digest);
    }
    Ok(AddedSingletonInductiveReceipt {
        family,
        constructors,
        recursor,
        source_declaration_sha256: source_digests,
        target_declaration_sha256: target_digests,
    })
}

struct AdmittedDeclarations {
    definitions: Vec<AddedDefinitionReceipt>,
    theorems: Vec<AddedTheoremReceipt>,
    singleton_inductives: Vec<AddedSingletonInductiveReceipt>,
}

fn admit_missing_declarations_in_dependency_order(
    source: &Kernel,
    target: &mut Kernel,
    missing: &[NameId],
    packages: &[SingletonInductivePackage],
) -> Result<AdmittedDeclarations, CheckedTheoremCompositionError> {
    let mut translator = ExpressionTranslator::new(source, target);
    let mut definitions = Vec::new();
    let mut theorems = Vec::new();
    let packages_by_family = packages
        .iter()
        .map(|package| (package.family, package))
        .collect::<BTreeMap<_, _>>();
    let package_members = packages
        .iter()
        .flat_map(|package| {
            std::iter::once(package.family)
                .chain(package.constructors.iter().copied())
                .chain(std::iter::once(package.recursor))
        })
        .collect::<BTreeSet<_>>();
    let mut singleton_inductives = Vec::new();
    for &source_name in missing {
        if let Some(package) = packages_by_family.get(&source_name) {
            singleton_inductives.push(admit_one_singleton_inductive(
                source,
                &mut translator,
                package,
            )?);
            continue;
        }
        if package_members.contains(&source_name) {
            continue;
        }
        let declaration = source
            .environment()
            .get(source_name)
            .ok_or_else(|| {
                CheckedTheoremCompositionError::Identity(
                    "missing source declaration disappeared".to_owned(),
                )
            })?
            .clone();
        match declaration {
            declaration @ Declaration::Definition { .. } => definitions.push(admit_one_definition(
                &mut translator,
                source_name,
                declaration,
            )?),
            declaration @ Declaration::Theorem { .. } => {
                theorems.push(admit_one_theorem(
                    &mut translator,
                    source_name,
                    declaration,
                )?);
            }
            _ => {}
        }
    }
    Ok(AdmittedDeclarations {
        definitions,
        theorems,
        singleton_inductives,
    })
}

fn admit_one_definition(
    translator: &mut ExpressionTranslator<'_>,
    source_name: NameId,
    declaration: Declaration,
) -> Result<AddedDefinitionReceipt, CheckedTheoremCompositionError> {
    let rendered = translator.source.display_name(source_name).to_string();
    let hint = match &declaration {
        Declaration::Definition { hint, .. } => *hint,
        _ => unreachable!("dispatcher selects only definitions"),
    };
    let translated = translator.definition(declaration)?;
    translator
        .target
        .add_declaration(translated)
        .map_err(|error| CheckedTheoremCompositionError::AdmissionRejected {
            name: rendered.clone(),
            error: explain_admission_error(translator.target, &error),
        })?;
    let target_name = admitted_target_name(translator.target, &rendered, "definition")?;
    Ok(AddedDefinitionReceipt {
        name: rendered,
        source_declaration_sha256: declaration_sha256(translator.source, source_name)?,
        target_declaration_sha256: declaration_sha256(translator.target, target_name)?,
        reducibility: reducibility_receipt(hint),
    })
}

fn admit_one_theorem(
    translator: &mut ExpressionTranslator<'_>,
    source_name: NameId,
    declaration: Declaration,
) -> Result<AddedTheoremReceipt, CheckedTheoremCompositionError> {
    let rendered = translator.source.display_name(source_name).to_string();
    let translated = translator.theorem(declaration)?;
    translator
        .target
        .add_declaration(translated)
        .map_err(|error| CheckedTheoremCompositionError::AdmissionRejected {
            name: rendered.clone(),
            error: explain_admission_error(translator.target, &error),
        })?;
    let target_name = admitted_target_name(translator.target, &rendered, "theorem")?;
    let axiom_footprint = translator
        .target
        .axiom_footprint(target_name)
        .into_iter()
        .map(|name| translator.target.display_name(name).to_string())
        .collect();
    Ok(AddedTheoremReceipt {
        name: rendered,
        source_declaration_sha256: declaration_sha256(translator.source, source_name)?,
        target_declaration_sha256: declaration_sha256(translator.target, target_name)?,
        axiom_footprint,
    })
}

/// Render arena-owned expression payloads before the private target is
/// discarded. Raw `ExprId`s are process-local and cannot identify a semantic
/// mismatch in a durable decline receipt.
fn explain_admission_error(target: &mut Kernel, error: &KernelError) -> String {
    match error {
        KernelError::TypeMismatch { expected, got } => {
            let expected_rendered = target.render_lean(*expected);
            let got_rendered = target.render_lean(*got);
            let expected_whnf = target.whnf(*expected);
            let got_whnf = target.whnf(*got);
            let (first_expected, first_got) =
                first_defeq_mismatch(target, expected_whnf, got_whnf, 0);
            let first_expected_whnf = target.whnf(first_expected);
            let first_got_whnf = target.whnf(first_got);
            format!(
                "TypeMismatch {{ expected: {expected_rendered:?}, got: {got_rendered:?}, expected_whnf: {:?}, got_whnf: {:?}, first_expected: {:?}, first_got: {:?}, first_expected_whnf: {:?}, first_got_whnf: {:?} }}",
                target.render_lean(expected_whnf),
                target.render_lean(got_whnf),
                target.render_lean(first_expected),
                target.render_lean(first_got),
                target.render_lean(first_expected_whnf),
                target.render_lean(first_got_whnf)
            )
        }
        KernelError::DeclarationValueMismatch { declared, inferred } => format!(
            "DeclarationValueMismatch {{ declared: {:?}, inferred: {:?} }}",
            target.render_lean(*declared),
            target.render_lean(*inferred)
        ),
        _ => format!("{error:?}"),
    }
}

fn first_defeq_mismatch(
    target: &mut Kernel,
    expected: ExprId,
    got: ExprId,
    depth: usize,
) -> (ExprId, ExprId) {
    if depth >= 64 || target.def_eq(expected, got) {
        return (expected, got);
    }
    let expected = target.whnf(expected);
    let got = target.whnf(got);
    match (
        target.expr_node(expected).clone(),
        target.expr_node(got).clone(),
    ) {
        (ExprNode::App(expected_fn, expected_arg), ExprNode::App(got_fn, got_arg)) => {
            if target.def_eq(expected_fn, got_fn) {
                first_defeq_mismatch(target, expected_arg, got_arg, depth + 1)
            } else {
                first_defeq_mismatch(target, expected_fn, got_fn, depth + 1)
            }
        }
        _ => (expected, got),
    }
}

fn admitted_target_name(
    target: &Kernel,
    rendered: &str,
    kind: &str,
) -> Result<NameId, CheckedTheoremCompositionError> {
    declaration_names(target)
        .get(rendered)
        .copied()
        .ok_or_else(|| {
            CheckedTheoremCompositionError::Identity(format!(
                "admitted {kind} is absent from target: {rendered}"
            ))
        })
}

fn reducibility_receipt(hint: ReducibilityHint) -> String {
    match hint {
        ReducibilityHint::Opaque => "opaque".to_owned(),
        ReducibilityHint::Regular(height) => format!("regular:{height}"),
        ReducibilityHint::Abbrev => "abbrev".to_owned(),
    }
}

struct ExpressionTranslator<'a> {
    source: &'a Kernel,
    target: &'a mut Kernel,
    names: HashMap<NameId, NameId>,
    levels: HashMap<LevelId, LevelId>,
    expressions: HashMap<ExprId, ExprId>,
}

impl<'a> ExpressionTranslator<'a> {
    fn new(source: &'a Kernel, target: &'a mut Kernel) -> Self {
        Self {
            source,
            target,
            names: HashMap::new(),
            levels: HashMap::new(),
            expressions: HashMap::new(),
        }
    }

    fn theorem(
        &mut self,
        declaration: Declaration,
    ) -> Result<Declaration, CheckedTheoremCompositionError> {
        let Declaration::Theorem {
            name,
            uparams,
            ty,
            value,
        } = declaration
        else {
            unreachable!("missing declaration kinds are rejected before translation")
        };
        Ok(Declaration::Theorem {
            name: self.name(name),
            uparams: uparams.into_iter().map(|name| self.name(name)).collect(),
            ty: self.expr(ty)?,
            value: self.expr(value)?,
        })
    }

    fn definition(
        &mut self,
        declaration: Declaration,
    ) -> Result<Declaration, CheckedTheoremCompositionError> {
        let Declaration::Definition {
            name,
            uparams,
            ty,
            value,
            hint,
        } = declaration
        else {
            unreachable!("missing declaration kinds are dispatched before translation")
        };
        Ok(Declaration::Definition {
            name: self.name(name),
            uparams: uparams.into_iter().map(|name| self.name(name)).collect(),
            ty: self.expr(ty)?,
            value: self.expr(value)?,
            hint,
        })
    }

    fn name(&mut self, source: NameId) -> NameId {
        if let Some(&translated) = self.names.get(&source) {
            return translated;
        }
        let translated = match self.source.name_node(source).clone() {
            NameNode::Anonymous => self.target.anon(),
            NameNode::Str(parent, component) => {
                let parent = self.name(parent);
                self.target.name_str(parent, component)
            }
            NameNode::Num(parent, component) => {
                let parent = self.name(parent);
                self.target.name_num(parent, component)
            }
        };
        self.names.insert(source, translated);
        translated
    }

    fn level(&mut self, source: LevelId) -> LevelId {
        if let Some(&translated) = self.levels.get(&source) {
            return translated;
        }
        let translated = match self.source.level_node(source).clone() {
            LevelNode::Zero => self.target.level_zero(),
            LevelNode::Succ(level) => {
                let level = self.level(level);
                self.target.level_succ(level)
            }
            LevelNode::Max(left, right) => {
                let left = self.level(left);
                let right = self.level(right);
                self.target.level_max(left, right)
            }
            LevelNode::IMax(left, right) => {
                let left = self.level(left);
                let right = self.level(right);
                self.target.level_imax(left, right)
            }
            LevelNode::Param(name) => {
                let name = self.name(name);
                self.target.level_param(name)
            }
        };
        self.levels.insert(source, translated);
        translated
    }

    fn expr(&mut self, source: ExprId) -> Result<ExprId, CheckedTheoremCompositionError> {
        if let Some(&translated) = self.expressions.get(&source) {
            return Ok(translated);
        }
        let translated = match self.source.expr_node(source).clone() {
            ExprNode::BVar(index) => self.target.bvar(index),
            ExprNode::FVar(_) => return Err(CheckedTheoremCompositionError::FreeVariable),
            ExprNode::Sort(level) => {
                let level = self.level(level);
                self.target.sort(level)
            }
            ExprNode::Const(name, levels) => {
                let name = self.name(name);
                let levels = levels.into_iter().map(|level| self.level(level)).collect();
                self.target.const_(name, levels)
            }
            ExprNode::Proj(name, index, structure) => {
                let name = self.name(name);
                let structure = self.expr(structure)?;
                self.target.proj(name, index, structure)
            }
            ExprNode::App(function, argument) => {
                let function = self.expr(function)?;
                let argument = self.expr(argument)?;
                self.target.app(function, argument)
            }
            ExprNode::Lam(name, ty, body, info) => {
                let name = self.name(name);
                let ty = self.expr(ty)?;
                let body = self.expr(body)?;
                self.target.lam(name, ty, body, info)
            }
            ExprNode::Pi(name, ty, body, info) => {
                let name = self.name(name);
                let ty = self.expr(ty)?;
                let body = self.expr(body)?;
                self.target.pi(name, ty, body, info)
            }
            ExprNode::Let(name, ty, value, body) => {
                let name = self.name(name);
                let ty = self.expr(ty)?;
                let value = self.expr(value)?;
                let body = self.expr(body)?;
                self.target.let_(name, ty, value, body)
            }
            ExprNode::Lit(literal) => self.target.lit(literal),
        };
        self.expressions.insert(source, translated);
        Ok(translated)
    }
}

fn declaration_names(kernel: &Kernel) -> BTreeMap<String, NameId> {
    kernel
        .environment()
        .iter()
        .map(|(&name, _)| (kernel.display_name(name).to_string(), name))
        .collect()
}

fn declaration_kind(declaration: &Declaration) -> &'static str {
    match declaration {
        Declaration::Axiom { .. } => "axiom",
        Declaration::Definition { .. } => "definition",
        Declaration::Theorem { .. } => "theorem",
        Declaration::Opaque { .. } => "opaque",
        Declaration::Inductive { .. } => "inductive",
        Declaration::Constructor { .. } => "constructor",
        Declaration::Recursor { .. } => "recursor",
        Declaration::Quotient { .. } => "quotient",
    }
}

fn type_shape(
    kernel: &Kernel,
    expression: ExprId,
) -> Result<String, CheckedTheoremCompositionError> {
    canonical_kernel_type_shape_sha256(kernel, expression)
        .map_err(CheckedTheoremCompositionError::Identity)
}

fn declaration_sha256(
    kernel: &Kernel,
    name: NameId,
) -> Result<String, CheckedTheoremCompositionError> {
    canonical_declaration_sha256(kernel, name).map_err(CheckedTheoremCompositionError::Identity)
}

fn environment_sha256(kernel: &Kernel) -> Result<String, CheckedTheoremCompositionError> {
    let mut entries: Vec<(String, String)> = kernel
        .environment()
        .iter()
        .map(|(&name, _)| {
            Ok((
                kernel.display_name(name).to_string(),
                declaration_sha256(kernel, name)?,
            ))
        })
        .collect::<Result<_, CheckedTheoremCompositionError>>()?;
    entries.sort();
    let mut hasher = Sha256::new();
    hasher.update(b"axeyum.checked-theorem-composition.environment.v1\0");
    for (name, digest) in entries {
        hasher.update((name.len() as u64).to_le_bytes());
        hasher.update(name.as_bytes());
        hasher.update(digest.as_bytes());
    }
    Ok(hex_sha256(&hasher.finalize()))
}

fn hex_sha256(bytes: &[u8]) -> String {
    let digest = Sha256::digest(bytes);
    let mut hex = String::with_capacity(digest.len() * 2);
    for byte in digest {
        let _ = write!(hex, "{byte:02x}");
    }
    hex
}

#[cfg(test)]
mod tests;
