//! Checked specialization of a theorem already admitted in one kernel.
//!
//! The operation applies named declarations to a generic theorem in a private
//! clone, asks the kernel to infer the resulting proposition and admit the
//! specialized proof, and publishes the clone only when the new theorem has an
//! empty kernel-derived axiom footprint. The receipt can be replayed from the
//! unchanged input environment.

use std::fmt;

use axeyum_lean_kernel::{Declaration, Kernel, NameId};
use serde_json::{Value, json};
use sha2::{Digest, Sha256};

use crate::canonical_declaration_sha256;

/// Version of the checked theorem-specialization receipt.
pub const CHECKED_THEOREM_SPECIALIZATION_VERSION: &str = "axeyum.checked-theorem-specialization.v1";

/// One declaration used as a specialization argument.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SpecializationArgumentReceipt {
    /// Zero-based application position.
    pub position: usize,
    /// Complete rendered declaration name.
    pub name: String,
    /// Exact declaration identity in the input kernel.
    pub declaration_sha256: String,
}

/// Replayable receipt for one checked theorem specialization.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CheckedTheoremSpecializationReceipt {
    /// Receipt and policy version.
    pub schema_version: String,
    /// Generic theorem applied by the operation.
    pub source_theorem: String,
    /// Exact identity of the generic theorem.
    pub source_theorem_sha256: String,
    /// Ordered checked declarations applied to the generic theorem.
    pub arguments: Vec<SpecializationArgumentReceipt>,
    /// Newly admitted theorem name.
    pub target_theorem: String,
    /// Exact identity of the independently admitted theorem.
    pub target_theorem_sha256: String,
    /// Kernel-derived assumptions reached by the specialized theorem.
    pub axiom_footprint: Vec<String>,
    /// Exact environment identity before specialization.
    pub environment_sha256_before: String,
    /// Exact environment identity after specialization.
    pub environment_sha256_after: String,
    /// Canonical digest of every preceding field.
    pub receipt_sha256: String,
}

impl CheckedTheoremSpecializationReceipt {
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
            "source_theorem": self.source_theorem,
            "source_theorem_sha256": self.source_theorem_sha256,
            "arguments": self.arguments.iter().map(|argument| json!({
                "position": argument.position,
                "name": argument.name,
                "declaration_sha256": argument.declaration_sha256,
            })).collect::<Vec<_>>(),
            "target_theorem": self.target_theorem,
            "target_theorem_sha256": self.target_theorem_sha256,
            "axiom_footprint": self.axiom_footprint,
            "environment_sha256_before": self.environment_sha256_before,
            "environment_sha256_after": self.environment_sha256_after,
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

/// An owned environment published only after specialization passes.
#[derive(Debug)]
pub struct CompletedTheoremSpecialization {
    kernel: Kernel,
    receipt: CheckedTheoremSpecializationReceipt,
}

impl CompletedTheoremSpecialization {
    /// Borrow the independently checked completed target.
    #[must_use]
    pub fn kernel(&self) -> &Kernel {
        &self.kernel
    }

    /// Borrow the replayable specialization receipt.
    #[must_use]
    pub fn receipt(&self) -> &CheckedTheoremSpecializationReceipt {
        &self.receipt
    }

    /// Transfer ownership of the checked target and its matching receipt.
    #[must_use]
    pub fn into_parts(self) -> (Kernel, CheckedTheoremSpecializationReceipt) {
        (self.kernel, self.receipt)
    }
}

/// A fail-closed theorem-specialization decline.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CheckedTheoremSpecializationError {
    /// A supplied declaration handle does not exist in the input environment.
    MissingDeclaration(String),
    /// The source declaration is not a checked theorem.
    SourceIsNotTheorem(String),
    /// The target already has a declaration.
    TargetExists(String),
    /// Type inference or theorem admission rejected the application.
    Kernel(String),
    /// The admitted theorem reaches one or more assumptions.
    NonEmptyAxiomFootprint(Vec<String>),
    /// Canonical identity derivation failed.
    Identity(String),
    /// A supplied receipt or completed environment did not reproduce.
    ReceiptMismatch,
}

impl fmt::Display for CheckedTheoremSpecializationError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{self:?}")
    }
}

impl std::error::Error for CheckedTheoremSpecializationError {}

/// Apply checked declarations to a generic theorem and independently admit the
/// resulting specialized theorem in a private kernel clone.
///
/// `source_theorem`, every `arguments` handle, and `target_theorem` must belong
/// to `kernel`. The target name may be interned but must not already name a
/// declaration. Neither an application/type error nor an assumption-bearing
/// result can mutate the caller's environment.
///
/// # Errors
///
/// Returns a typed decline for missing declarations, a non-theorem source, an
/// existing target, kernel rejection, non-empty footprint, or identity failure.
pub fn specialize_checked_theorem(
    kernel: &Kernel,
    source_theorem: NameId,
    arguments: &[NameId],
    target_theorem: NameId,
) -> Result<CompletedTheoremSpecialization, CheckedTheoremSpecializationError> {
    let source_declaration = kernel.environment().get(source_theorem).ok_or_else(|| {
        CheckedTheoremSpecializationError::MissingDeclaration(format!("{source_theorem:?}"))
    })?;
    let source_name = kernel.display_name(source_theorem).to_string();
    if !matches!(source_declaration, Declaration::Theorem { .. }) {
        return Err(CheckedTheoremSpecializationError::SourceIsNotTheorem(
            source_name,
        ));
    }
    let target_name = kernel.display_name(target_theorem).to_string();
    if kernel.environment().contains(target_theorem) {
        return Err(CheckedTheoremSpecializationError::TargetExists(target_name));
    }

    let mut argument_receipts = Vec::with_capacity(arguments.len());
    for (position, &argument) in arguments.iter().enumerate() {
        kernel.environment().get(argument).ok_or_else(|| {
            CheckedTheoremSpecializationError::MissingDeclaration(format!("{argument:?}"))
        })?;
        argument_receipts.push(SpecializationArgumentReceipt {
            position,
            name: kernel.display_name(argument).to_string(),
            declaration_sha256: canonical_declaration_sha256(kernel, argument)
                .map_err(|error| CheckedTheoremSpecializationError::Identity(error.clone()))?,
        });
    }

    let before = environment_sha256(kernel)?;
    let source_sha256 = canonical_declaration_sha256(kernel, source_theorem)
        .map_err(|error| CheckedTheoremSpecializationError::Identity(error.clone()))?;
    let mut staged = kernel.clone();
    let mut proof = staged.const_(source_theorem, vec![]);
    for &argument in arguments {
        let constant = staged.const_(argument, vec![]);
        proof = staged.app(proof, constant);
    }
    let ty = staged
        .infer(proof)
        .map_err(|error| CheckedTheoremSpecializationError::Kernel(format!("{error:?}")))?;
    staged
        .add_declaration(Declaration::Theorem {
            name: target_theorem,
            uparams: vec![],
            ty,
            value: proof,
        })
        .map_err(|error| CheckedTheoremSpecializationError::Kernel(format!("{error:?}")))?;
    let axiom_footprint = staged
        .axiom_footprint(target_theorem)
        .iter()
        .map(|&name| staged.display_name(name).to_string())
        .collect::<Vec<_>>();
    if !axiom_footprint.is_empty() {
        return Err(CheckedTheoremSpecializationError::NonEmptyAxiomFootprint(
            axiom_footprint,
        ));
    }
    let target_sha256 = canonical_declaration_sha256(&staged, target_theorem)
        .map_err(|error| CheckedTheoremSpecializationError::Identity(error.clone()))?;
    let after = environment_sha256(&staged)?;
    let mut receipt = CheckedTheoremSpecializationReceipt {
        schema_version: CHECKED_THEOREM_SPECIALIZATION_VERSION.to_owned(),
        source_theorem: source_name,
        source_theorem_sha256: source_sha256,
        arguments: argument_receipts,
        target_theorem: target_name,
        target_theorem_sha256: target_sha256,
        axiom_footprint,
        environment_sha256_before: before,
        environment_sha256_after: after,
        receipt_sha256: String::new(),
    };
    let payload = serde_json::to_vec(&receipt.json_value(false))
        .map_err(|error| CheckedTheoremSpecializationError::Identity(error.to_string()))?;
    receipt.receipt_sha256 = hex_sha256(&payload);
    Ok(CompletedTheoremSpecialization {
        kernel: staged,
        receipt,
    })
}

/// Replay a specialization and require the receipt and completed environment
/// identities to match exactly.
///
/// # Errors
///
/// Returns the original specialization decline or `ReceiptMismatch` when the
/// supplied receipt or completed environment does not reproduce.
pub fn verify_checked_theorem_specialization(
    kernel: &Kernel,
    completed: &Kernel,
    source_theorem: NameId,
    arguments: &[NameId],
    target_theorem: NameId,
    receipt: &CheckedTheoremSpecializationReceipt,
) -> Result<(), CheckedTheoremSpecializationError> {
    if !receipt.has_valid_digest() {
        return Err(CheckedTheoremSpecializationError::ReceiptMismatch);
    }
    let reproduced = specialize_checked_theorem(kernel, source_theorem, arguments, target_theorem)?;
    let completed_identity = environment_sha256(completed)?;
    if reproduced.receipt != *receipt
        || completed_identity != receipt.environment_sha256_after
        || reproduced.receipt.environment_sha256_after != receipt.environment_sha256_after
    {
        return Err(CheckedTheoremSpecializationError::ReceiptMismatch);
    }
    Ok(())
}

fn hex_sha256(bytes: &[u8]) -> String {
    let digest = Sha256::digest(bytes);
    let mut rendered = String::with_capacity(digest.len() * 2);
    for byte in digest {
        use std::fmt::Write as _;
        write!(rendered, "{byte:02x}").expect("writing to a String cannot fail");
    }
    rendered
}

fn environment_sha256(kernel: &Kernel) -> Result<String, CheckedTheoremSpecializationError> {
    let mut entries = kernel
        .environment()
        .iter()
        .map(|(&name, _)| {
            Ok((
                kernel.display_name(name).to_string(),
                canonical_declaration_sha256(kernel, name)
                    .map_err(|error| CheckedTheoremSpecializationError::Identity(error.clone()))?,
            ))
        })
        .collect::<Result<Vec<_>, CheckedTheoremSpecializationError>>()?;
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

#[cfg(test)]
mod tests {
    use super::*;
    use axeyum_lean_kernel::{BinderInfo, build_logic_prelude};

    struct Fixture {
        kernel: Kernel,
        generic: NameId,
        identity: NameId,
        wrong: NameId,
        target: NameId,
        assumption: NameId,
        assumption_consumer: NameId,
        assumption_target: NameId,
    }

    fn fixture() -> Fixture {
        let mut kernel = Kernel::new();
        let logic = build_logic_prelude(&mut kernel).expect("logic prelude builds");
        let anon = kernel.anon();
        let nat = kernel.const_(logic.nat, vec![]);
        let function_ty = kernel.pi(anon, nat, nat, BinderInfo::Default);
        let identity = kernel.name_str(anon, "specializationIdentity");
        let identity_body = kernel.bvar(0);
        let identity_value = kernel.lam(anon, nat, identity_body, BinderInfo::Default);
        kernel
            .add_declaration(Declaration::Definition {
                name: identity,
                uparams: vec![],
                ty: function_ty,
                value: identity_value,
                hint: axeyum_lean_kernel::ReducibilityHint::Regular(0),
            })
            .expect("identity definition checks");
        let wrong = logic.nat_zero;

        let generic = kernel.name_str(anon, "specializationGeneric");
        let function = kernel.bvar(1);
        let value = kernel.bvar(0);
        let applied = kernel.app(function, value);
        let zero = kernel.level_zero();
        let one = kernel.level_succ(zero);
        let eq = kernel.const_(logic.eq, vec![one]);
        let eq = kernel.app(eq, nat);
        let eq = kernel.app(eq, applied);
        let goal = kernel.app(eq, applied);
        let body = kernel.const_(logic.eq_refl, vec![one]);
        let body = kernel.app(body, nat);
        let body = kernel.app(body, applied);
        let generic_ty = kernel.pi(anon, nat, goal, BinderInfo::Default);
        let generic_ty = kernel.pi(anon, function_ty, generic_ty, BinderInfo::Default);
        let generic_value = kernel.lam(anon, nat, body, BinderInfo::Default);
        let generic_value = kernel.lam(anon, function_ty, generic_value, BinderInfo::Default);
        kernel
            .add_declaration(Declaration::Theorem {
                name: generic,
                uparams: vec![],
                ty: generic_ty,
                value: generic_value,
            })
            .expect("generic theorem checks");
        let target = kernel.name_str(anon, "specializationTarget");
        let true_ty = kernel.const_(logic.true_, vec![]);
        let assumption = kernel.name_str(anon, "specializationAssumption");
        kernel
            .add_declaration(Declaration::Axiom {
                name: assumption,
                uparams: vec![],
                ty: true_ty,
            })
            .expect("assumption control checks");
        let assumption_consumer = kernel.name_str(anon, "specializationAssumptionConsumer");
        let assumption_consumer_ty = kernel.pi(anon, true_ty, true_ty, BinderInfo::Default);
        let assumption_consumer_body = kernel.bvar(0);
        let assumption_consumer_value =
            kernel.lam(anon, true_ty, assumption_consumer_body, BinderInfo::Default);
        kernel
            .add_declaration(Declaration::Theorem {
                name: assumption_consumer,
                uparams: vec![],
                ty: assumption_consumer_ty,
                value: assumption_consumer_value,
            })
            .expect("assumption consumer checks without reaching the control axiom");
        let assumption_target = kernel.name_str(anon, "specializationAssumptionTarget");
        Fixture {
            kernel,
            generic,
            identity,
            wrong,
            target,
            assumption,
            assumption_consumer,
            assumption_target,
        }
    }

    #[test]
    fn specialization_is_checked_footprint_free_and_replayable() {
        let fixture = fixture();
        let before = fixture.kernel.environment().len();
        let completed = specialize_checked_theorem(
            &fixture.kernel,
            fixture.generic,
            &[fixture.identity],
            fixture.target,
        )
        .expect("well-typed specialization succeeds");
        assert_eq!(fixture.kernel.environment().len(), before);
        assert_eq!(completed.kernel().environment().len(), before + 1);
        assert!(completed.receipt().axiom_footprint.is_empty());
        assert!(completed.receipt().has_valid_digest());
        verify_checked_theorem_specialization(
            &fixture.kernel,
            completed.kernel(),
            fixture.generic,
            &[fixture.identity],
            fixture.target,
            completed.receipt(),
        )
        .expect("receipt replays");
    }

    #[test]
    fn wrong_argument_is_rejected_without_mutating_the_caller() {
        let fixture = fixture();
        let before = fixture.kernel.environment().len();
        let error = specialize_checked_theorem(
            &fixture.kernel,
            fixture.generic,
            &[fixture.wrong],
            fixture.target,
        )
        .expect_err("Nat.zero cannot fill a Nat-to-Nat function binder");
        assert!(matches!(
            error,
            CheckedTheoremSpecializationError::Kernel(_)
        ));
        assert_eq!(fixture.kernel.environment().len(), before);
        assert!(!fixture.kernel.environment().contains(fixture.target));
    }

    #[test]
    fn receipt_mutation_is_rejected() {
        let fixture = fixture();
        let completed = specialize_checked_theorem(
            &fixture.kernel,
            fixture.generic,
            &[fixture.identity],
            fixture.target,
        )
        .expect("well-typed specialization succeeds");
        let mut receipt = completed.receipt().clone();
        receipt.target_theorem_sha256 = "mutated".to_owned();
        assert_eq!(
            verify_checked_theorem_specialization(
                &fixture.kernel,
                completed.kernel(),
                fixture.generic,
                &[fixture.identity],
                fixture.target,
                &receipt,
            ),
            Err(CheckedTheoremSpecializationError::ReceiptMismatch)
        );
    }

    #[test]
    fn assumption_bearing_specialization_is_rejected_without_publication() {
        let fixture = fixture();
        let before = fixture.kernel.environment().len();
        let error = specialize_checked_theorem(
            &fixture.kernel,
            fixture.assumption_consumer,
            &[fixture.assumption],
            fixture.assumption_target,
        )
        .expect_err("an assumption-bearing application must not publish");
        assert_eq!(
            error,
            CheckedTheoremSpecializationError::NonEmptyAxiomFootprint(vec![
                "specializationAssumption".to_owned()
            ])
        );
        assert_eq!(fixture.kernel.environment().len(), before);
        assert!(
            !fixture
                .kernel
                .environment()
                .contains(fixture.assumption_target)
        );
    }

    #[test]
    fn existing_target_is_rejected() {
        let fixture = fixture();
        let error = specialize_checked_theorem(
            &fixture.kernel,
            fixture.generic,
            &[fixture.identity],
            fixture.identity,
        )
        .expect_err("an existing declaration cannot be overwritten");
        assert!(matches!(
            error,
            CheckedTheoremSpecializationError::TargetExists(_)
        ));
    }
}
