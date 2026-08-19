//! Durable replay receipt for a residualized source contract and one bounded delta step.

use std::fmt;

use axeyum_lean_kernel::{Declaration, ExprId, ExprNode, Kernel, NameId};
use serde_json::{Value, json};
use sha2::{Digest, Sha256};

use crate::{
    ConstantInstance, build_source_delta_step, canonical_declaration_sha256,
    canonical_expression_sha256, canonical_level_sha256, residualize_function_contract_body,
};

/// Schema for ADR-0491's first trace-backed source-contract receipt.
pub const TRACE_BACKED_SOURCE_CONTRACT_RECEIPT_VERSION: &str =
    "axeyum-trace-backed-source-contract-receipt-v1";

/// One exact source, residual, or retained constant instance bound by a receipt.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TraceContractInstanceReceipt {
    /// Stable role: `source`, `residual`, or `retained`.
    pub role: &'static str,
    /// Exact rendered declaration name.
    pub name: String,
    /// Caller-selected local binder name; retained instances use an empty value.
    pub binder_name: String,
    /// Canonical hashes of exact universe arguments in order.
    pub level_sha256: Vec<String>,
    /// Canonical structural declaration identity.
    pub content_sha256: String,
    /// Canonical identity of the exact instantiated constant type.
    pub instantiated_type_sha256: String,
}

/// Replayable evidence that one exact source definition instantiates one
/// proof-free residualized function contract by a bounded structural delta step.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TraceBackedSourceContractReceipt {
    /// Stable receipt schema.
    pub schema_version: &'static str,
    /// Caller-owned selection/derivation policy identity.
    pub policy_version: String,
    /// Exact selected source definition instance.
    pub source: TraceContractInstanceReceipt,
    /// Exact residual function/data instances in dependency order.
    pub residual: Vec<TraceContractInstanceReceipt>,
    /// Exact retained body instances in caller order.
    pub retained: Vec<TraceContractInstanceReceipt>,
    /// Number of pointwise source arguments exposed by residualization.
    pub function_arity: usize,
    /// Source plus residual binder count.
    pub contract_binders: usize,
    /// Canonical exact-source equation identity.
    pub source_equation_sha256: String,
    /// Canonical proof-free generalized contract identity.
    pub generalized_contract_sha256: String,
    /// Stable bounded reduction rule.
    pub delta_rule: &'static str,
    /// Canonical source constant before the selected delta step.
    pub delta_before_sha256: String,
    /// Canonical stored source body after the selected delta step.
    pub delta_after_sha256: String,
    /// Exact declaration consulted by the structural delta checker.
    pub consulted_declarations: Vec<String>,
    /// Complete source axiom footprint; version 1 requires this to be empty.
    pub source_axiom_footprint: Vec<String>,
    /// Canonical digest of every preceding field.
    pub receipt_sha256: String,
}

impl TraceBackedSourceContractReceipt {
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
        let instance_json = |instance: &TraceContractInstanceReceipt| {
            json!({
                "role": instance.role,
                "name": instance.name,
                "binder_name": instance.binder_name,
                "level_sha256": instance.level_sha256,
                "content_sha256": instance.content_sha256,
                "instantiated_type_sha256": instance.instantiated_type_sha256,
            })
        };
        let mut value = json!({
            "schema_version": self.schema_version,
            "policy_version": self.policy_version,
            "source": instance_json(&self.source),
            "residual": self.residual.iter().map(&instance_json).collect::<Vec<_>>(),
            "retained": self.retained.iter().map(&instance_json).collect::<Vec<_>>(),
            "contract": {
                "function_arity": self.function_arity,
                "binders": self.contract_binders,
                "source_equation_sha256": self.source_equation_sha256,
                "generalized_sha256": self.generalized_contract_sha256,
            },
            "delta": {
                "rule": self.delta_rule,
                "before_sha256": self.delta_before_sha256,
                "after_sha256": self.delta_after_sha256,
                "consulted_declarations": self.consulted_declarations,
            },
            "source_axiom_footprint": self.source_axiom_footprint,
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

/// A trace-backed source-contract receipt could not be issued or replayed.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TraceBackedSourceContractReceiptError {
    /// The caller-owned policy identity was empty.
    EmptyPolicy,
    /// A supplied direct body instance was trusted/proof-bearing rather than
    /// proof-free data or computation.
    TrustedDirectInstance {
        /// Exact rendered declaration name.
        name: String,
        /// Stable declaration kind.
        kind: &'static str,
    },
    /// Residualization, specialization, or bounded delta checking declined.
    Contract(String),
    /// The generalized template retained an exact source or residual constant.
    TemplateRetainedGeneralizedInstance {
        /// Exact rendered declaration name.
        name: String,
    },
    /// The selected source retained one or more trusted assumptions.
    SourceAxiomFootprint {
        /// Stable sorted rendered axiom names.
        names: Vec<String>,
    },
    /// Canonical identity construction failed.
    Identity(String),
    /// A transported receipt was stale or mutated.
    ReceiptMismatch,
}

impl fmt::Display for TraceBackedSourceContractReceiptError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::EmptyPolicy => write!(formatter, "trace-backed contract policy is empty"),
            Self::TrustedDirectInstance { name, kind } => {
                write!(
                    formatter,
                    "trace-backed contract instance {name} is trusted kind {kind}"
                )
            }
            Self::Contract(error) => write!(formatter, "trace-backed contract failed: {error}"),
            Self::TemplateRetainedGeneralizedInstance { name } => write!(
                formatter,
                "trace-backed contract template retained generalized instance {name}"
            ),
            Self::SourceAxiomFootprint { names } => write!(
                formatter,
                "trace-backed contract source retains axioms: {}",
                names.join(",")
            ),
            Self::Identity(error) => write!(formatter, "trace-backed identity failed: {error}"),
            Self::ReceiptMismatch => write!(formatter, "trace-backed contract receipt changed"),
        }
    }
}

impl std::error::Error for TraceBackedSourceContractReceiptError {}

/// Issue one source-contract receipt from a checked source kernel.
///
/// This certifies only the exact residualized contract and selected structural
/// delta step. It does not create a theorem witness or authorize a theorem or
/// ledger transition.
///
/// # Errors
///
/// Fails closed on empty policy, trusted direct instances, source assumptions,
/// residualization/specialization/delta failure, retained generalized
/// instances, or canonical identity failure.
#[allow(clippy::too_many_lines)]
pub fn issue_trace_backed_source_contract_receipt(
    kernel: &mut Kernel,
    source: &ConstantInstance,
    residual: &[ConstantInstance],
    retained: &[ConstantInstance],
    policy_version: &str,
) -> Result<TraceBackedSourceContractReceipt, TraceBackedSourceContractReceiptError> {
    if policy_version.is_empty() {
        return Err(TraceBackedSourceContractReceiptError::EmptyPolicy);
    }
    for instance in residual.iter().chain(retained) {
        reject_trusted_instance(kernel, instance)?;
    }
    let contract = residualize_function_contract_body(kernel, source, residual, retained)
        .map_err(|error| TraceBackedSourceContractReceiptError::Contract(error.to_string()))?;
    for instance in std::iter::once(source).chain(residual) {
        if contains_instance(kernel, contract.generalized.goal, instance) {
            return Err(
                TraceBackedSourceContractReceiptError::TemplateRetainedGeneralizedInstance {
                    name: kernel.display_name(instance.name).to_string(),
                },
            );
        }
    }
    let delta = build_source_delta_step(kernel, source.name, &source.levels, &[])
        .map_err(|error| TraceBackedSourceContractReceiptError::Contract(error.to_string()))?;
    let source_axiom_footprint = rendered_names(kernel, &kernel.axiom_footprint(source.name));
    if !source_axiom_footprint.is_empty() {
        return Err(
            TraceBackedSourceContractReceiptError::SourceAxiomFootprint {
                names: source_axiom_footprint,
            },
        );
    }
    let source_name = kernel.display_name(source.name).to_string();
    let mut receipt = TraceBackedSourceContractReceipt {
        schema_version: TRACE_BACKED_SOURCE_CONTRACT_RECEIPT_VERSION,
        policy_version: policy_version.to_owned(),
        source: instance_receipt(kernel, source, "source")?,
        residual: residual
            .iter()
            .map(|instance| instance_receipt(kernel, instance, "residual"))
            .collect::<Result<_, _>>()?,
        retained: retained
            .iter()
            .map(|instance| instance_receipt(kernel, instance, "retained"))
            .collect::<Result<_, _>>()?,
        function_arity: contract.function_arity,
        contract_binders: contract.generalized.binders.len(),
        source_equation_sha256: canonical_expression_sha256(kernel, contract.source_equation)
            .map_err(TraceBackedSourceContractReceiptError::Identity)?,
        generalized_contract_sha256: canonical_expression_sha256(kernel, contract.generalized.goal)
            .map_err(TraceBackedSourceContractReceiptError::Identity)?,
        delta_rule: "selected-transparent-definition-delta-v1",
        delta_before_sha256: canonical_expression_sha256(kernel, delta.before)
            .map_err(TraceBackedSourceContractReceiptError::Identity)?,
        delta_after_sha256: canonical_expression_sha256(kernel, delta.after)
            .map_err(TraceBackedSourceContractReceiptError::Identity)?,
        consulted_declarations: vec![source_name],
        source_axiom_footprint,
        receipt_sha256: String::new(),
    };
    let payload = serde_json::to_vec(&receipt.json_value(false))
        .map_err(|error| TraceBackedSourceContractReceiptError::Identity(error.to_string()))?;
    receipt.receipt_sha256 = hex_sha256(&payload);
    Ok(receipt)
}

/// Reissue a receipt from the current kernel and compare every field.
///
/// # Errors
///
/// Returns the issue-time failure or
/// [`TraceBackedSourceContractReceiptError::ReceiptMismatch`] for a stale or
/// mutated receipt.
pub fn verify_trace_backed_source_contract_receipt(
    receipt: &TraceBackedSourceContractReceipt,
    kernel: &mut Kernel,
    source: &ConstantInstance,
    residual: &[ConstantInstance],
    retained: &[ConstantInstance],
) -> Result<(), TraceBackedSourceContractReceiptError> {
    if !receipt.has_valid_digest() {
        return Err(TraceBackedSourceContractReceiptError::ReceiptMismatch);
    }
    let reissued = issue_trace_backed_source_contract_receipt(
        kernel,
        source,
        residual,
        retained,
        &receipt.policy_version,
    )?;
    if &reissued != receipt {
        return Err(TraceBackedSourceContractReceiptError::ReceiptMismatch);
    }
    Ok(())
}

fn reject_trusted_instance(
    kernel: &Kernel,
    instance: &ConstantInstance,
) -> Result<(), TraceBackedSourceContractReceiptError> {
    let Some(declaration) = kernel.environment().get(instance.name) else {
        return Err(TraceBackedSourceContractReceiptError::Identity(format!(
            "missing declaration {}",
            kernel.display_name(instance.name)
        )));
    };
    let kind = match declaration {
        Declaration::Axiom { .. } => Some("axiom"),
        Declaration::Theorem { .. } => Some("theorem"),
        Declaration::Opaque { .. } => Some("opaque"),
        Declaration::Definition { .. }
        | Declaration::Inductive { .. }
        | Declaration::Constructor { .. }
        | Declaration::Recursor { .. }
        | Declaration::Quotient { .. } => None,
    };
    if let Some(kind) = kind {
        return Err(
            TraceBackedSourceContractReceiptError::TrustedDirectInstance {
                name: kernel.display_name(instance.name).to_string(),
                kind,
            },
        );
    }
    Ok(())
}

fn instance_receipt(
    kernel: &mut Kernel,
    instance: &ConstantInstance,
    role: &'static str,
) -> Result<TraceContractInstanceReceipt, TraceBackedSourceContractReceiptError> {
    let term = kernel.const_(instance.name, instance.levels.clone());
    let ty = kernel.infer(term).map_err(|error| {
        TraceBackedSourceContractReceiptError::Identity(format!(
            "{} instance type: {error:?}",
            kernel.display_name(instance.name)
        ))
    })?;
    Ok(TraceContractInstanceReceipt {
        role,
        name: kernel.display_name(instance.name).to_string(),
        binder_name: if role == "retained" {
            String::new()
        } else {
            kernel.display_name(instance.binder_name).to_string()
        },
        level_sha256: instance
            .levels
            .iter()
            .map(|&level| canonical_level_sha256(kernel, level))
            .collect(),
        content_sha256: canonical_declaration_sha256(kernel, instance.name)
            .map_err(TraceBackedSourceContractReceiptError::Identity)?,
        instantiated_type_sha256: canonical_expression_sha256(kernel, ty)
            .map_err(TraceBackedSourceContractReceiptError::Identity)?,
    })
}

fn contains_instance(kernel: &Kernel, root: ExprId, instance: &ConstantInstance) -> bool {
    let mut seen = std::collections::HashSet::new();
    let mut pending = vec![root];
    while let Some(expression) = pending.pop() {
        if !seen.insert(expression) {
            continue;
        }
        match kernel.expr_node(expression) {
            ExprNode::Const(name, levels)
                if *name == instance.name && *levels == instance.levels =>
            {
                return true;
            }
            ExprNode::App(function, argument)
            | ExprNode::Lam(_, function, argument, _)
            | ExprNode::Pi(_, function, argument, _) => pending.extend([*function, *argument]),
            ExprNode::Let(_, ty, value, body) => pending.extend([*ty, *value, *body]),
            ExprNode::Proj(_, _, structure) => pending.push(*structure),
            ExprNode::BVar(_)
            | ExprNode::FVar(_)
            | ExprNode::Sort(_)
            | ExprNode::Lit(_)
            | ExprNode::Const(_, _) => {}
        }
    }
    false
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
