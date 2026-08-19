//! Durable replay receipt for an exact-source discharged function contract.

use std::fmt;

use axeyum_lean_kernel::{Declaration, ExprId, ExprNode, Kernel, NameId};
use serde_json::{Value, json};
use sha2::{Digest, Sha256};

use crate::{canonical_declaration_sha256, canonical_expression_sha256};

/// Receipt schema for ADR-0488's first pointwise function-contract boundary.
pub const SEMANTIC_FUNCTION_CONTRACT_RECEIPT_VERSION: &str =
    "axeyum-semantic-function-contract-receipt-v1";

/// One exact declaration in a theorem's complete transitive dependency closure.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SemanticContractDependencyReceipt {
    /// Exact rendered declaration name.
    pub name: String,
    /// Stable declaration kind.
    pub kind: String,
    /// Canonical structural declaration identity.
    pub content_sha256: String,
}

/// Source-bound evidence that a local pointwise contract was independently
/// proved for one exact definition and used to recover one concrete theorem.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SemanticFunctionContractReceipt {
    /// Stable receipt schema.
    pub schema_version: &'static str,
    /// Caller-owned proposal/selection policy identity.
    pub policy_version: String,
    /// Exact rendered source definition name.
    pub source_name: String,
    /// Canonical source declaration identity.
    pub source_content_sha256: String,
    /// Canonical source function-type identity.
    pub source_type_sha256: String,
    /// The source function is the outermost generic theorem binder.
    pub source_binder_position: usize,
    /// The behavior contract is the next generic theorem binder.
    pub contract_binder_position: usize,
    /// Canonical identity of the contract after exact-source specialization.
    pub specialized_contract_sha256: String,
    /// Exact rendered generic theorem name.
    pub generic_theorem: String,
    /// Canonical generic theorem identity in the proof-isolated kernel.
    pub generic_theorem_content_sha256: String,
    /// Canonical generic theorem type identity.
    pub generic_theorem_type_sha256: String,
    /// Canonical generic proof-term identity.
    pub generic_proof_sha256: String,
    /// Complete generic theorem dependency closure.
    pub generic_dependencies: Vec<SemanticContractDependencyReceipt>,
    /// Exact rendered source-specialization witness theorem name.
    pub source_witness: String,
    /// Canonical witness theorem identity.
    pub source_witness_content_sha256: String,
    /// Canonical witness proof-term identity.
    pub source_witness_proof_sha256: String,
    /// Complete witness dependency closure, including the exact source definition.
    pub source_witness_dependencies: Vec<SemanticContractDependencyReceipt>,
    /// Canonical proposition obtained by applying the generic theorem to the
    /// exact source definition and witness.
    pub specialized_goal_sha256: String,
    /// Exact rendered concrete theorem name.
    pub concrete_theorem: String,
    /// Canonical concrete theorem identity.
    pub concrete_theorem_content_sha256: String,
    /// Canonical concrete proof-term identity.
    pub concrete_proof_sha256: String,
    /// Complete concrete theorem dependency closure.
    pub concrete_dependencies: Vec<SemanticContractDependencyReceipt>,
    /// Complete axiom footprint; version 1 requires this to be empty.
    pub axiom_footprint: Vec<String>,
    /// Direct/transitive theorem dependencies of the concrete theorem.
    pub theorem_dependencies: Vec<String>,
    /// Canonical digest of every preceding field.
    pub receipt_sha256: String,
}

impl SemanticFunctionContractReceipt {
    /// Recompute the canonical receipt payload digest.
    #[must_use]
    pub fn has_valid_digest(&self) -> bool {
        serde_json::to_vec(&self.json_value(false))
            .is_ok_and(|payload| hex_sha256(&payload) == self.receipt_sha256)
    }

    /// Render stable pretty JSON for durable external storage.
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
        let dependency_json = |dependencies: &[SemanticContractDependencyReceipt]| {
            dependencies
                .iter()
                .map(|dependency| {
                    json!({
                        "name": dependency.name,
                        "kind": dependency.kind,
                        "content_sha256": dependency.content_sha256,
                    })
                })
                .collect::<Vec<_>>()
        };
        let mut value = json!({
            "schema_version": self.schema_version,
            "policy_version": self.policy_version,
            "source": {
                "name": self.source_name,
                "content_sha256": self.source_content_sha256,
                "type_sha256": self.source_type_sha256,
                "binder_position": self.source_binder_position,
            },
            "contract": {
                "binder_position": self.contract_binder_position,
                "specialized_sha256": self.specialized_contract_sha256,
            },
            "generic": {
                "theorem": self.generic_theorem,
                "content_sha256": self.generic_theorem_content_sha256,
                "type_sha256": self.generic_theorem_type_sha256,
                "proof_sha256": self.generic_proof_sha256,
                "dependencies": dependency_json(&self.generic_dependencies),
            },
            "source_witness": {
                "theorem": self.source_witness,
                "content_sha256": self.source_witness_content_sha256,
                "proof_sha256": self.source_witness_proof_sha256,
                "dependencies": dependency_json(&self.source_witness_dependencies),
            },
            "specialized_goal_sha256": self.specialized_goal_sha256,
            "concrete": {
                "theorem": self.concrete_theorem,
                "content_sha256": self.concrete_theorem_content_sha256,
                "proof_sha256": self.concrete_proof_sha256,
                "dependencies": dependency_json(&self.concrete_dependencies),
                "axiom_footprint": self.axiom_footprint,
                "theorem_dependencies": self.theorem_dependencies,
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

/// A semantic contract receipt could not be issued or replayed.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SemanticFunctionContractReceiptError {
    /// The caller-owned policy identity was empty.
    EmptyPolicy,
    /// A named role was absent or had the wrong declaration kind.
    WrongDeclarationKind {
        /// Stable role label.
        role: &'static str,
    },
    /// Version 1 accepts only monomorphic transparent source definitions.
    PolymorphicSource,
    /// The proof-kernel generic theorem and source-kernel mirror differed.
    GenericMirrorMismatch,
    /// The generic proof kernel retained an axiom or another theorem.
    GenericProofNotIndependent,
    /// The outer source binder or following local contract binder was malformed.
    ContractTelescopeMismatch,
    /// The exact source definition did not inhabit the generic source binder.
    SourceTypeMismatch,
    /// The witness did not prove the exact-source-specialized contract.
    WitnessTypeMismatch,
    /// The witness retained an axiom or another theorem.
    WitnessNotIndependent,
    /// Applying the generic proof, exact source, and witness did not recover the
    /// concrete theorem's proposition.
    SpecializedGoalMismatch,
    /// The concrete theorem did not contain that exact checked application.
    ConcreteProofMismatch,
    /// The concrete result retained trusted assumptions.
    ConcreteAxiomFootprint,
    /// The concrete theorem dependency set was not exactly generic plus witness.
    ConcreteTheoremDependencies,
    /// Canonical identity construction failed.
    Identity(String),
    /// A transported receipt was stale or mutated.
    ReceiptMismatch,
}

impl fmt::Display for SemanticFunctionContractReceiptError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::EmptyPolicy => write!(formatter, "semantic contract policy is empty"),
            Self::WrongDeclarationKind { role } => {
                write!(
                    formatter,
                    "semantic contract {role} has the wrong declaration kind"
                )
            }
            Self::PolymorphicSource => write!(formatter, "semantic contract source is polymorphic"),
            Self::GenericMirrorMismatch => write!(formatter, "generic theorem mirror changed"),
            Self::GenericProofNotIndependent => {
                write!(
                    formatter,
                    "generic proof is not theorem- and axiom-independent"
                )
            }
            Self::ContractTelescopeMismatch => write!(formatter, "contract telescope changed"),
            Self::SourceTypeMismatch => write!(formatter, "source function binder type changed"),
            Self::WitnessTypeMismatch => write!(formatter, "source witness contract type changed"),
            Self::WitnessNotIndependent => {
                write!(
                    formatter,
                    "source witness is not theorem- and axiom-independent"
                )
            }
            Self::SpecializedGoalMismatch => write!(formatter, "specialized goal changed"),
            Self::ConcreteProofMismatch => write!(formatter, "concrete proof application changed"),
            Self::ConcreteAxiomFootprint => write!(formatter, "concrete theorem has axioms"),
            Self::ConcreteTheoremDependencies => {
                write!(formatter, "concrete theorem dependency set changed")
            }
            Self::Identity(error) => write!(formatter, "canonical identity failed: {error}"),
            Self::ReceiptMismatch => write!(formatter, "semantic contract receipt changed"),
        }
    }
}

impl std::error::Error for SemanticFunctionContractReceiptError {}

/// Issue one receipt after independently checking both proof and source kernels.
///
/// The source kernel must contain a byte-for-byte semantic mirror of the generic
/// theorem so the concrete theorem can apply it. The proof kernel supplies the
/// independent assurance boundary; the source kernel supplies the exact
/// definition, discharged contract witness, and concrete specialization.
///
/// # Errors
///
/// Fails closed on any declaration, identity, binder, type, proof, dependency,
/// or axiom-footprint mismatch.
#[allow(clippy::too_many_arguments, clippy::too_many_lines)]
pub fn issue_semantic_function_contract_receipt(
    proof_kernel: &mut Kernel,
    proof_generic: NameId,
    source_kernel: &mut Kernel,
    source_definition: NameId,
    source_generic: NameId,
    source_witness: NameId,
    concrete_theorem: NameId,
    policy_version: &str,
) -> Result<SemanticFunctionContractReceipt, SemanticFunctionContractReceiptError> {
    if policy_version.is_empty() {
        return Err(SemanticFunctionContractReceiptError::EmptyPolicy);
    }
    let (proof_generic_type, proof_generic_value) =
        theorem_parts(proof_kernel, proof_generic, "proof generic")?;
    let (source_generic_type, source_generic_value) =
        theorem_parts(source_kernel, source_generic, "source generic")?;
    let (source_type, source_uparams) = definition_type(source_kernel, source_definition)?;
    if !source_uparams.is_empty() {
        return Err(SemanticFunctionContractReceiptError::PolymorphicSource);
    }
    let proof_generic_content = declaration_hash(proof_kernel, proof_generic)?;
    let source_generic_content = declaration_hash(source_kernel, source_generic)?;
    if proof_generic_content != source_generic_content
        || expression_hash(proof_kernel, proof_generic_type)?
            != expression_hash(source_kernel, source_generic_type)?
        || expression_hash(proof_kernel, proof_generic_value)?
            != expression_hash(source_kernel, source_generic_value)?
    {
        return Err(SemanticFunctionContractReceiptError::GenericMirrorMismatch);
    }
    if !proof_kernel.axiom_footprint(proof_generic).is_empty()
        || !transitive_theorem_dependencies(proof_kernel, proof_generic).is_empty()
    {
        return Err(SemanticFunctionContractReceiptError::GenericProofNotIndependent);
    }

    let generic_type = source_kernel.whnf(source_generic_type);
    let ExprNode::Pi(_, generic_source_type, after_source, _) =
        *source_kernel.expr_node(generic_type)
    else {
        return Err(SemanticFunctionContractReceiptError::ContractTelescopeMismatch);
    };
    if !source_kernel.def_eq(generic_source_type, source_type) {
        return Err(SemanticFunctionContractReceiptError::SourceTypeMismatch);
    }
    let source_term = source_kernel.const_(source_definition, vec![]);
    let after_source = source_kernel.instantiate(after_source, &[source_term]);
    let after_source = source_kernel.whnf(after_source);
    let ExprNode::Pi(_, specialized_contract, _, _) = *source_kernel.expr_node(after_source) else {
        return Err(SemanticFunctionContractReceiptError::ContractTelescopeMismatch);
    };

    let (witness_type, witness_value) =
        theorem_parts(source_kernel, source_witness, "source witness")?;
    if !source_kernel.def_eq(witness_type, specialized_contract) {
        return Err(SemanticFunctionContractReceiptError::WitnessTypeMismatch);
    }
    if !source_kernel.axiom_footprint(source_witness).is_empty()
        || !transitive_theorem_dependencies(source_kernel, source_witness).is_empty()
    {
        return Err(SemanticFunctionContractReceiptError::WitnessNotIndependent);
    }

    let (concrete_type, concrete_value) =
        theorem_parts(source_kernel, concrete_theorem, "concrete theorem")?;
    let generic_term = source_kernel.const_(source_generic, vec![]);
    let applied_source = source_kernel.app(generic_term, source_term);
    let witness_term = source_kernel.const_(source_witness, vec![]);
    let specialized_proof = source_kernel.app(applied_source, witness_term);
    let specialized_type = source_kernel.infer(specialized_proof).map_err(|error| {
        SemanticFunctionContractReceiptError::Identity(format!("specialized proof: {error:?}"))
    })?;
    if !source_kernel.def_eq(specialized_type, concrete_type) {
        return Err(SemanticFunctionContractReceiptError::SpecializedGoalMismatch);
    }
    if concrete_value != specialized_proof {
        return Err(SemanticFunctionContractReceiptError::ConcreteProofMismatch);
    }
    let axiom_footprint = rendered_names(
        source_kernel,
        &source_kernel.axiom_footprint(concrete_theorem),
    );
    if !axiom_footprint.is_empty() {
        return Err(SemanticFunctionContractReceiptError::ConcreteAxiomFootprint);
    }
    let theorem_dependencies = rendered_names(
        source_kernel,
        &transitive_theorem_dependencies(source_kernel, concrete_theorem),
    );
    let mut expected_theorems = vec![
        source_kernel.display_name(source_generic).to_string(),
        source_kernel.display_name(source_witness).to_string(),
    ];
    expected_theorems.sort();
    expected_theorems.dedup();
    if theorem_dependencies != expected_theorems {
        return Err(SemanticFunctionContractReceiptError::ConcreteTheoremDependencies);
    }

    let mut receipt = SemanticFunctionContractReceipt {
        schema_version: SEMANTIC_FUNCTION_CONTRACT_RECEIPT_VERSION,
        policy_version: policy_version.to_owned(),
        source_name: source_kernel.display_name(source_definition).to_string(),
        source_content_sha256: declaration_hash(source_kernel, source_definition)?,
        source_type_sha256: expression_hash(source_kernel, source_type)?,
        source_binder_position: 0,
        contract_binder_position: 1,
        specialized_contract_sha256: expression_hash(source_kernel, specialized_contract)?,
        generic_theorem: proof_kernel.display_name(proof_generic).to_string(),
        generic_theorem_content_sha256: proof_generic_content,
        generic_theorem_type_sha256: expression_hash(proof_kernel, proof_generic_type)?,
        generic_proof_sha256: expression_hash(proof_kernel, proof_generic_value)?,
        generic_dependencies: dependency_receipts(proof_kernel, proof_generic)?,
        source_witness: source_kernel.display_name(source_witness).to_string(),
        source_witness_content_sha256: declaration_hash(source_kernel, source_witness)?,
        source_witness_proof_sha256: expression_hash(source_kernel, witness_value)?,
        source_witness_dependencies: dependency_receipts(source_kernel, source_witness)?,
        specialized_goal_sha256: expression_hash(source_kernel, specialized_type)?,
        concrete_theorem: source_kernel.display_name(concrete_theorem).to_string(),
        concrete_theorem_content_sha256: declaration_hash(source_kernel, concrete_theorem)?,
        concrete_proof_sha256: expression_hash(source_kernel, concrete_value)?,
        concrete_dependencies: dependency_receipts(source_kernel, concrete_theorem)?,
        axiom_footprint,
        theorem_dependencies,
        receipt_sha256: String::new(),
    };
    let payload = serde_json::to_vec(&receipt.json_value(false))
        .map_err(|error| SemanticFunctionContractReceiptError::Identity(error.to_string()))?;
    receipt.receipt_sha256 = hex_sha256(&payload);
    Ok(receipt)
}

/// Independently reissue the receipt from current kernels and compare every field.
///
/// # Errors
///
/// Returns the issue-time failure or [`SemanticFunctionContractReceiptError::ReceiptMismatch`]
/// for a stale, reordered, or mutated receipt.
#[allow(clippy::too_many_arguments)]
pub fn verify_semantic_function_contract_receipt(
    receipt: &SemanticFunctionContractReceipt,
    proof_kernel: &mut Kernel,
    proof_generic: NameId,
    source_kernel: &mut Kernel,
    source_definition: NameId,
    source_generic: NameId,
    source_witness: NameId,
    concrete_theorem: NameId,
) -> Result<(), SemanticFunctionContractReceiptError> {
    if !receipt.has_valid_digest() {
        return Err(SemanticFunctionContractReceiptError::ReceiptMismatch);
    }
    let reissued = issue_semantic_function_contract_receipt(
        proof_kernel,
        proof_generic,
        source_kernel,
        source_definition,
        source_generic,
        source_witness,
        concrete_theorem,
        &receipt.policy_version,
    )?;
    if &reissued != receipt {
        return Err(SemanticFunctionContractReceiptError::ReceiptMismatch);
    }
    Ok(())
}

fn theorem_parts(
    kernel: &Kernel,
    name: NameId,
    role: &'static str,
) -> Result<(ExprId, ExprId), SemanticFunctionContractReceiptError> {
    match kernel.environment().get(name) {
        Some(Declaration::Theorem { ty, value, .. }) => Ok((*ty, *value)),
        _ => Err(SemanticFunctionContractReceiptError::WrongDeclarationKind { role }),
    }
}

fn definition_type(
    kernel: &Kernel,
    name: NameId,
) -> Result<(ExprId, Vec<NameId>), SemanticFunctionContractReceiptError> {
    match kernel.environment().get(name) {
        Some(Declaration::Definition { ty, uparams, .. }) => Ok((*ty, uparams.clone())),
        _ => Err(SemanticFunctionContractReceiptError::WrongDeclarationKind { role: "source" }),
    }
}

fn dependency_receipts(
    kernel: &Kernel,
    root: NameId,
) -> Result<Vec<SemanticContractDependencyReceipt>, SemanticFunctionContractReceiptError> {
    kernel
        .declaration_dependency_closure(root)
        .into_iter()
        .map(|name| {
            let declaration = kernel.environment().get(name).ok_or_else(|| {
                SemanticFunctionContractReceiptError::Identity("dependency disappeared".to_owned())
            })?;
            Ok(SemanticContractDependencyReceipt {
                name: kernel.display_name(name).to_string(),
                kind: declaration_kind(declaration).to_owned(),
                content_sha256: declaration_hash(kernel, name)?,
            })
        })
        .collect()
}

fn transitive_theorem_dependencies(kernel: &Kernel, root: NameId) -> Vec<NameId> {
    kernel
        .declaration_dependency_closure(root)
        .into_iter()
        .filter(|&name| {
            matches!(
                kernel.environment().get(name),
                Some(Declaration::Theorem { .. })
            )
        })
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

fn declaration_hash(
    kernel: &Kernel,
    name: NameId,
) -> Result<String, SemanticFunctionContractReceiptError> {
    canonical_declaration_sha256(kernel, name)
        .map_err(SemanticFunctionContractReceiptError::Identity)
}

fn expression_hash(
    kernel: &Kernel,
    expression: ExprId,
) -> Result<String, SemanticFunctionContractReceiptError> {
    canonical_expression_sha256(kernel, expression)
        .map_err(SemanticFunctionContractReceiptError::Identity)
}

fn rendered_names(kernel: &Kernel, names: &[NameId]) -> Vec<String> {
    names
        .iter()
        .map(|&name| kernel.display_name(name).to_string())
        .collect()
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
