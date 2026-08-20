//! Checked theorem-rooted composition between independently owned kernels.
//!
//! This module implements ADR-0523's publication boundary. Compatibility only
//! authorizes an attempt; the target kernel independently checks every rebuilt
//! proof before the completed clone is published.

use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::fmt;
use std::fmt::Write as _;

use axeyum_lean_kernel::{
    Declaration, ExprId, ExprNode, Kernel, LevelId, LevelNode, NameId, NameNode,
};
use serde_json::{Value, json};
use sha2::{Digest, Sha256};

use crate::{canonical_declaration_sha256, canonical_kernel_type_shape_sha256};

/// Version of the checked theorem-composition receipt and compatibility policy.
pub const CHECKED_THEOREM_COMPOSITION_VERSION: &str = "axeyum.checked-theorem-composition.v3";

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

/// One atomically reconstructed non-recursive singleton inductive package.
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

/// Deterministic receipt for one completed theorem-only composition.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CheckedTheoremCompositionReceipt {
    /// Compatibility, translation, and receipt schema.
    pub schema_version: String,
    /// Explicit roots requested by the caller, in caller order.
    pub roots: Vec<String>,
    /// Root-selected source closure in dependency order.
    pub source_closure: Vec<String>,
    /// Exact target environment identity before composition.
    pub target_environment_sha256_before: String,
    /// Existing target declarations reused after type-shape validation.
    pub reused_declarations: Vec<ReusedDeclarationReceipt>,
    /// Missing source theorems independently admitted to the target clone.
    pub added_theorems: Vec<AddedTheoremReceipt>,
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
            "added_singleton_inductives": self.added_singleton_inductives.iter().map(|row| json!({
                "family": row.family,
                "constructors": row.constructors,
                "recursor": row.recursor,
                "source_declaration_sha256": row.source_declaration_sha256,
                "target_declaration_sha256": row.target_declaration_sha256,
            })).collect::<Vec<_>>(),
            "target_environment_sha256_after": self.target_environment_sha256_after,
        });
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
    /// The current schema admits only missing checked theorems and complete
    /// non-recursive singleton inductive packages.
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
    /// The requested closure would add no declaration.
    NoAdditions,
    /// Canonical identity derivation failed.
    Identity(String),
    /// A supplied receipt or completed environment did not reproduce.
    ReceiptMismatch,
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
/// before cloning, admits every missing theorem into the private clone, and
/// returns the clone only after the complete slice succeeds.
///
/// # Errors
///
/// Declines on invalid roots, incompatible reused types, unsupported or partial
/// missing declaration packages, non-closed terms, identity failures, or a
/// trusted-gate rejection. Complete non-recursive singleton inductives are
/// reconstructed atomically before missing theorem admission. No error
/// publishes a target kernel.
pub fn compose_checked_theorem_slice(
    source: &Kernel,
    target: &Kernel,
    roots: &[&str],
) -> Result<CompletedTheoremComposition, CheckedTheoremCompositionError> {
    let selected = select_closure(source, roots)?;
    let target_names = declaration_names(target);
    let reused = validate_reused(source, target, &selected, &target_names)?;
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
    let added_singleton_inductives =
        admit_missing_singleton_inductives(source, &mut staged, &singleton_packages)?;
    let missing_theorems = missing
        .iter()
        .copied()
        .filter(|name| {
            matches!(
                source.environment().get(*name),
                Some(Declaration::Theorem { .. })
            )
        })
        .collect::<Vec<_>>();
    let added = admit_missing_theorems(source, &mut staged, &missing_theorems)?;
    let after = environment_sha256(&staged)?;
    let mut receipt = CheckedTheoremCompositionReceipt {
        schema_version: CHECKED_THEOREM_COMPOSITION_VERSION.to_owned(),
        roots: roots.iter().map(|root| (*root).to_owned()).collect(),
        source_closure: selected
            .iter()
            .map(|name| source.display_name(*name).to_string())
            .collect(),
        target_environment_sha256_before: before,
        reused_declarations: reused,
        added_theorems: added,
        added_singleton_inductives,
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

fn select_closure(
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
    source
        .root_declaration_closure(&root_ids)
        .map_err(|error| CheckedTheoremCompositionError::Closure(format!("{error:?}")))
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
        if !matches!(declaration, Declaration::Theorem { .. }) && !package_members.contains(&name) {
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
    if *is_recursive {
        return Err(
            CheckedTheoremCompositionError::UnsupportedMissingDeclaration {
                name: rendered,
                kind: "recursive-inductive".to_owned(),
            },
        );
    }
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
    Ok(SingletonInductivePackage {
        family,
        constructors: ctor_names.clone(),
        recursor,
    })
}

fn admit_missing_singleton_inductives(
    source: &Kernel,
    target: &mut Kernel,
    packages: &[SingletonInductivePackage],
) -> Result<Vec<AddedSingletonInductiveReceipt>, CheckedTheoremCompositionError> {
    let mut translator = ExpressionTranslator::new(source, target);
    let mut added = Vec::new();
    for package in packages {
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
                error: format!("{error:?}"),
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
            source_digests.insert(rendered.clone(), declaration_sha256(source, source_name)?);
            target_digests.insert(
                rendered,
                declaration_sha256(translator.target, target_name)?,
            );
        }
        added.push(AddedSingletonInductiveReceipt {
            family,
            constructors,
            recursor,
            source_declaration_sha256: source_digests,
            target_declaration_sha256: target_digests,
        });
    }
    Ok(added)
}

fn admit_missing_theorems(
    source: &Kernel,
    target: &mut Kernel,
    missing: &[NameId],
) -> Result<Vec<AddedTheoremReceipt>, CheckedTheoremCompositionError> {
    let mut translator = ExpressionTranslator::new(source, target);
    let mut added = Vec::new();
    for &source_name in missing {
        let rendered = source.display_name(source_name).to_string();
        let declaration = source
            .environment()
            .get(source_name)
            .ok_or_else(|| {
                CheckedTheoremCompositionError::Identity(
                    "missing source declaration disappeared".to_owned(),
                )
            })?
            .clone();
        let translated = translator.theorem(declaration)?;
        translator
            .target
            .add_declaration(translated)
            .map_err(|error| CheckedTheoremCompositionError::AdmissionRejected {
                name: rendered.clone(),
                error: format!("{error:?}"),
            })?;
        let target_name = declaration_names(translator.target)
            .get(&rendered)
            .copied()
            .ok_or_else(|| {
                CheckedTheoremCompositionError::Identity(format!(
                    "admitted theorem is absent from target: {rendered}"
                ))
            })?;
        let axiom_footprint = translator
            .target
            .axiom_footprint(target_name)
            .into_iter()
            .map(|name| translator.target.display_name(name).to_string())
            .collect();
        added.push(AddedTheoremReceipt {
            name: rendered,
            source_declaration_sha256: declaration_sha256(source, source_name)?,
            target_declaration_sha256: declaration_sha256(translator.target, target_name)?,
            axiom_footprint,
        });
    }
    Ok(added)
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
