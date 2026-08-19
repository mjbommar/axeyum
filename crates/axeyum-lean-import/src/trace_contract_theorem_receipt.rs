//! Semantic theorem receipts derived from one replayed source-contract trace.

use std::fmt;

use axeyum_lean_kernel::{Declaration, ExprId, ExprNode, Kernel, NameId};
use serde_json::{Value, json};
use sha2::{Digest, Sha256};

use crate::{
    ConstantInstance, TraceBackedSourceContractReceipt, canonical_declaration_sha256,
    canonical_expression_sha256, residualize_function_contract_body,
    verify_trace_backed_source_contract_receipt,
};

/// Schema for the first trace-backed contract-to-theorem bridge.
pub const TRACE_BACKED_SEMANTIC_THEOREM_RECEIPT_VERSION: &str =
    "axeyum-trace-backed-semantic-theorem-receipt-v1";

const OPERATION: &str = "trace-contract-reflexivity-v1";
const MAX_BINDERS: usize = 2;
const MAX_CONSTRUCTED_NODES: usize = 5;

/// Replayable evidence that one bounded proof was independently admitted at
/// the exact equation authorized by a source-contract receipt.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TraceBackedSemanticTheoremReceipt {
    /// Stable receipt schema.
    pub schema_version: &'static str,
    /// Caller-owned frozen policy identity.
    pub policy_version: String,
    /// Digest of the exact source-contract receipt consumed by this bridge.
    pub source_contract_receipt_sha256: String,
    /// Canonical exact source equation identity.
    pub source_equation_sha256: String,
    /// Stable bounded construction operation.
    pub operation: &'static str,
    /// Number of pointwise binders introduced by the producer.
    pub binders: usize,
    /// Number of expression nodes constructed by the producer.
    pub constructed_nodes: usize,
    /// Exact admitted theorem name.
    pub theorem_name: String,
    /// Canonical theorem declaration identity.
    pub theorem_content_sha256: String,
    /// Canonical theorem type identity.
    pub theorem_type_sha256: String,
    /// Canonical constructed proof identity.
    pub proof_sha256: String,
    /// Complete theorem axiom footprint; version 1 requires this to be empty.
    pub axiom_footprint: Vec<String>,
    /// Direct theorem dependencies, retained only as diagnostic metadata.
    pub direct_theorem_dependencies: Vec<String>,
    /// Transitive theorem dependencies, retained only as diagnostic metadata.
    pub transitive_theorem_dependencies: Vec<String>,
    /// Canonical digest of every preceding field.
    pub receipt_sha256: String,
}

impl TraceBackedSemanticTheoremReceipt {
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
        let mut value = json!({
            "schema_version": self.schema_version,
            "policy_version": self.policy_version,
            "source_contract_receipt_sha256": self.source_contract_receipt_sha256,
            "source_equation_sha256": self.source_equation_sha256,
            "producer": {
                "operation": self.operation,
                "binders": self.binders,
                "constructed_nodes": self.constructed_nodes,
                "max_binders": MAX_BINDERS,
                "max_constructed_nodes": MAX_CONSTRUCTED_NODES,
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

/// A contract-backed semantic theorem receipt could not be issued or replayed.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TraceBackedSemanticTheoremReceiptError {
    /// The caller-owned policy identity was empty.
    EmptyPolicy,
    /// The source-contract receipt failed exact replay.
    SourceReceipt(String),
    /// Reconstructing the exact source equation failed.
    Contract(String),
    /// The frozen reflexivity grammar did not apply within its budget.
    Producer(String),
    /// The target name was already present at issue time.
    TargetExists,
    /// The independent kernel rejected the constructed theorem.
    Kernel(String),
    /// The admitted target was absent or not a theorem.
    WrongTargetKind,
    /// The theorem type or proof differed from the exact bounded construction.
    TheoremMismatch,
    /// The admitted theorem retained trusted assumptions.
    AxiomFootprint {
        /// Stable sorted rendered axiom names.
        names: Vec<String>,
    },
    /// Canonical identity construction failed.
    Identity(String),
    /// A transported theorem receipt was stale or mutated.
    ReceiptMismatch,
}

impl fmt::Display for TraceBackedSemanticTheoremReceiptError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::EmptyPolicy => write!(formatter, "semantic theorem policy is empty"),
            Self::SourceReceipt(error) => write!(formatter, "source receipt failed: {error}"),
            Self::Contract(error) => write!(formatter, "contract reconstruction failed: {error}"),
            Self::Producer(error) => write!(formatter, "bounded producer declined: {error}"),
            Self::TargetExists => write!(formatter, "semantic theorem target already exists"),
            Self::Kernel(error) => write!(formatter, "kernel rejected semantic theorem: {error}"),
            Self::WrongTargetKind => write!(formatter, "semantic theorem target is not a theorem"),
            Self::TheoremMismatch => {
                write!(formatter, "semantic theorem differs from construction")
            }
            Self::AxiomFootprint { names } => {
                write!(
                    formatter,
                    "semantic theorem retains axioms: {}",
                    names.join(",")
                )
            }
            Self::Identity(error) => write!(formatter, "semantic theorem identity failed: {error}"),
            Self::ReceiptMismatch => write!(formatter, "semantic theorem receipt changed"),
        }
    }
}

impl std::error::Error for TraceBackedSemanticTheoremReceiptError {}

/// Replay a source-contract receipt, construct its exact pointwise reflexivity
/// proof once, admit it through the independent kernel, and issue a theorem
/// receipt.
///
/// The dependency inventories are diagnostic: only exact source-receipt replay
/// and kernel acceptance authorize this theorem.
///
/// # Errors
///
/// Fails closed on stale source evidence, contract drift, grammar/budget drift,
/// an occupied target name, kernel rejection, axioms, or identity failure.
#[allow(clippy::too_many_arguments)]
pub fn issue_trace_backed_semantic_theorem_receipt(
    kernel: &mut Kernel,
    source_receipt: &TraceBackedSourceContractReceipt,
    source: &ConstantInstance,
    residual: &[ConstantInstance],
    retained: &[ConstantInstance],
    theorem_name: NameId,
    policy_version: &str,
) -> Result<TraceBackedSemanticTheoremReceipt, TraceBackedSemanticTheoremReceiptError> {
    if policy_version.is_empty() {
        return Err(TraceBackedSemanticTheoremReceiptError::EmptyPolicy);
    }
    if kernel.environment().get(theorem_name).is_some() {
        return Err(TraceBackedSemanticTheoremReceiptError::TargetExists);
    }
    let (goal, proof, binders, constructed_nodes) =
        reconstruct(kernel, source_receipt, source, residual, retained)?;
    kernel
        .add_declaration(Declaration::Theorem {
            name: theorem_name,
            uparams: vec![],
            ty: goal,
            value: proof,
        })
        .map_err(|error| TraceBackedSemanticTheoremReceiptError::Kernel(format!("{error:?}")))?;
    build_receipt(
        kernel,
        source_receipt,
        theorem_name,
        policy_version,
        goal,
        proof,
        binders,
        constructed_nodes,
    )
}

/// Replay both source and theorem receipts against an already admitted target.
///
/// # Errors
///
/// Returns the original issue-time failure or `ReceiptMismatch` for stale or
/// mutated theorem evidence.
#[allow(clippy::too_many_arguments)]
pub fn verify_trace_backed_semantic_theorem_receipt(
    receipt: &TraceBackedSemanticTheoremReceipt,
    kernel: &mut Kernel,
    source_receipt: &TraceBackedSourceContractReceipt,
    source: &ConstantInstance,
    residual: &[ConstantInstance],
    retained: &[ConstantInstance],
    theorem_name: NameId,
) -> Result<(), TraceBackedSemanticTheoremReceiptError> {
    if !receipt.has_valid_digest() {
        return Err(TraceBackedSemanticTheoremReceiptError::ReceiptMismatch);
    }
    let (goal, proof, binders, constructed_nodes) =
        reconstruct(kernel, source_receipt, source, residual, retained)?;
    let reissued = build_receipt(
        kernel,
        source_receipt,
        theorem_name,
        &receipt.policy_version,
        goal,
        proof,
        binders,
        constructed_nodes,
    )?;
    if &reissued != receipt {
        return Err(TraceBackedSemanticTheoremReceiptError::ReceiptMismatch);
    }
    Ok(())
}

fn reconstruct(
    kernel: &mut Kernel,
    source_receipt: &TraceBackedSourceContractReceipt,
    source: &ConstantInstance,
    residual: &[ConstantInstance],
    retained: &[ConstantInstance],
) -> Result<(ExprId, ExprId, usize, usize), TraceBackedSemanticTheoremReceiptError> {
    verify_trace_backed_source_contract_receipt(source_receipt, kernel, source, residual, retained)
        .map_err(|error| {
            TraceBackedSemanticTheoremReceiptError::SourceReceipt(error.to_string())
        })?;
    let contract = residualize_function_contract_body(kernel, source, residual, retained)
        .map_err(|error| TraceBackedSemanticTheoremReceiptError::Contract(error.to_string()))?;
    let (proof, binders, constructed_nodes) =
        construct_reflexivity(kernel, contract.source_equation)?;
    Ok((contract.source_equation, proof, binders, constructed_nodes))
}

fn construct_reflexivity(
    kernel: &mut Kernel,
    goal: ExprId,
) -> Result<(ExprId, usize, usize), TraceBackedSemanticTheoremReceiptError> {
    let mut telescope = Vec::new();
    let mut cursor = goal;
    while let ExprNode::Pi(name, ty, body, info) = kernel.expr_node(cursor) {
        if telescope.len() == MAX_BINDERS {
            return Err(TraceBackedSemanticTheoremReceiptError::Producer(
                "binder budget exceeded".to_owned(),
            ));
        }
        telescope.push((*name, *ty, *info));
        cursor = *body;
    }
    let (head, arguments) = app_spine(kernel, cursor);
    let ExprNode::Const(eq_name, levels) = kernel.expr_node(head) else {
        return Err(TraceBackedSemanticTheoremReceiptError::Producer(
            "terminal goal is not equality".to_owned(),
        ));
    };
    if kernel.display_name(*eq_name).to_string() != "Eq" || arguments.len() != 3 {
        return Err(TraceBackedSemanticTheoremReceiptError::Producer(
            "terminal goal is not exact Eq".to_owned(),
        ));
    }
    let levels = levels.clone();
    let eq_refl = exact_name(kernel, "Eq.refl")?;
    let mut proof = kernel.const_(eq_refl, levels);
    proof = kernel.app(proof, arguments[0]);
    proof = kernel.app(proof, arguments[1]);
    for (name, ty, info) in telescope.iter().rev() {
        proof = kernel.lam(*name, *ty, proof, *info);
    }
    let constructed_nodes = 3 + telescope.len();
    if constructed_nodes > MAX_CONSTRUCTED_NODES {
        return Err(TraceBackedSemanticTheoremReceiptError::Producer(
            "construction budget exceeded".to_owned(),
        ));
    }
    Ok((proof, telescope.len(), constructed_nodes))
}

#[allow(clippy::too_many_arguments)]
fn build_receipt(
    kernel: &mut Kernel,
    source_receipt: &TraceBackedSourceContractReceipt,
    theorem_name: NameId,
    policy_version: &str,
    expected_type: ExprId,
    expected_proof: ExprId,
    binders: usize,
    constructed_nodes: usize,
) -> Result<TraceBackedSemanticTheoremReceipt, TraceBackedSemanticTheoremReceiptError> {
    let Some(Declaration::Theorem { ty, value, .. }) = kernel.environment().get(theorem_name)
    else {
        return Err(TraceBackedSemanticTheoremReceiptError::WrongTargetKind);
    };
    let (ty, value) = (*ty, *value);
    if ty != expected_type || value != expected_proof {
        return Err(TraceBackedSemanticTheoremReceiptError::TheoremMismatch);
    }
    let axiom_footprint = rendered_names(kernel, &kernel.axiom_footprint(theorem_name));
    if !axiom_footprint.is_empty() {
        return Err(TraceBackedSemanticTheoremReceiptError::AxiomFootprint {
            names: axiom_footprint,
        });
    }
    let direct_theorem_dependencies =
        rendered_names(kernel, &kernel.theorem_dependencies(theorem_name));
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
    let mut receipt = TraceBackedSemanticTheoremReceipt {
        schema_version: TRACE_BACKED_SEMANTIC_THEOREM_RECEIPT_VERSION,
        policy_version: policy_version.to_owned(),
        source_contract_receipt_sha256: source_receipt.receipt_sha256.clone(),
        source_equation_sha256: canonical_expression_sha256(kernel, expected_type)
            .map_err(TraceBackedSemanticTheoremReceiptError::Identity)?,
        operation: OPERATION,
        binders,
        constructed_nodes,
        theorem_name: kernel.display_name(theorem_name).to_string(),
        theorem_content_sha256: canonical_declaration_sha256(kernel, theorem_name)
            .map_err(TraceBackedSemanticTheoremReceiptError::Identity)?,
        theorem_type_sha256: canonical_expression_sha256(kernel, ty)
            .map_err(TraceBackedSemanticTheoremReceiptError::Identity)?,
        proof_sha256: canonical_expression_sha256(kernel, value)
            .map_err(TraceBackedSemanticTheoremReceiptError::Identity)?,
        axiom_footprint,
        direct_theorem_dependencies,
        transitive_theorem_dependencies,
        receipt_sha256: String::new(),
    };
    let payload = serde_json::to_vec(&receipt.json_value(false))
        .map_err(|error| TraceBackedSemanticTheoremReceiptError::Identity(error.to_string()))?;
    receipt.receipt_sha256 = hex_sha256(&payload);
    Ok(receipt)
}

fn app_spine(kernel: &Kernel, mut expression: ExprId) -> (ExprId, Vec<ExprId>) {
    let mut arguments = Vec::new();
    while let ExprNode::App(function, argument) = kernel.expr_node(expression) {
        arguments.push(*argument);
        expression = *function;
    }
    arguments.reverse();
    (expression, arguments)
}

fn exact_name(
    kernel: &Kernel,
    rendered: &str,
) -> Result<NameId, TraceBackedSemanticTheoremReceiptError> {
    let matches: Vec<_> = kernel
        .environment()
        .iter()
        .filter_map(|(&name, _)| {
            (kernel.display_name(name).to_string() == rendered).then_some(name)
        })
        .collect();
    match matches.as_slice() {
        [name] => Ok(*name),
        _ => Err(TraceBackedSemanticTheoremReceiptError::Identity(format!(
            "required declaration {rendered} occurs {} times",
            matches.len()
        ))),
    }
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
