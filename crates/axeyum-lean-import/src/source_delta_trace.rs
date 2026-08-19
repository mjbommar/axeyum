//! Checked, bounded delta traces for one selected transparent definition.

use std::fmt;

use axeyum_lean_kernel::{Declaration, ExprId, ExprNode, Kernel, LevelId, NameId};

use crate::canonical_declaration_sha256;

/// Evidence for exactly one structural delta step.
///
/// The checker consults only `source`: constants occurring in `after` remain
/// opaque syntax and are not recursively unfolded or dependency-walked.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CheckedSourceDeltaStep {
    /// Exact selected definition.
    pub source: NameId,
    /// Canonical identity of that definition.
    pub source_content_sha256: String,
    /// Universe arguments on the source occurrence.
    pub levels: Vec<LevelId>,
    /// Application spine preserved across the step.
    pub arguments: Vec<ExprId>,
    /// Exact applied source expression before delta.
    pub before: ExprId,
    /// Exact instantiated body after one delta step.
    pub after: ExprId,
}

/// A proposed bounded source-delta step failed closed.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SourceDeltaStepError {
    /// The selected source is absent or is not a transparent definition.
    SourceNotDefinition,
    /// The proposed input is not headed by the exact selected source constant.
    SourceHeadMismatch,
    /// The source occurrence has the wrong number of universe arguments.
    UniverseArityMismatch {
        /// Number declared by the source definition.
        expected: usize,
        /// Number carried by the proposed source occurrence.
        observed: usize,
    },
    /// The proposed output is not the exact instantiated body with the same
    /// application spine.
    AfterMismatch,
    /// Canonical source identity construction failed.
    Identity(String),
}

impl fmt::Display for SourceDeltaStepError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::SourceNotDefinition => write!(formatter, "delta source is not a definition"),
            Self::SourceHeadMismatch => write!(formatter, "delta input has the wrong source head"),
            Self::UniverseArityMismatch { expected, observed } => write!(
                formatter,
                "delta source universe arity is {observed}, expected {expected}"
            ),
            Self::AfterMismatch => write!(formatter, "delta output is not the exact source body"),
            Self::Identity(error) => write!(formatter, "delta source identity failed: {error}"),
        }
    }
}

impl std::error::Error for SourceDeltaStepError {}

/// Construct and check one delta step for `source` at the supplied universe
/// and term arguments.
///
/// This does not normalize the resulting body. In particular, helper
/// definitions reached from the body stay opaque.
///
/// # Errors
///
/// Returns [`SourceDeltaStepError`] when `source` is not a transparent
/// definition, the universe arity is wrong, or canonical identity construction
/// fails.
pub fn build_source_delta_step(
    kernel: &mut Kernel,
    source: NameId,
    levels: &[LevelId],
    arguments: &[ExprId],
) -> Result<CheckedSourceDeltaStep, SourceDeltaStepError> {
    let mut before = kernel.const_(source, levels.to_vec());
    for &argument in arguments {
        before = kernel.app(before, argument);
    }
    let value = definition_value(kernel, source)?;
    let instantiated = instantiate_value(kernel, source, value, levels)?;
    let mut after = instantiated;
    for &argument in arguments {
        after = kernel.app(after, argument);
    }
    verify_source_delta_step(kernel, source, before, after)
}

/// Verify that `before -> after` is exactly one delta unfold of `source`.
///
/// The verification is structural: it reads the selected definition and
/// substitutes only its universe parameters. It performs no beta/iota/zeta
/// normalization, recursive delta unfolding, theorem lookup, or dependency
/// closure walk.
///
/// # Errors
///
/// Returns [`SourceDeltaStepError`] on the first source, head, universe,
/// output, or identity mismatch.
pub fn verify_source_delta_step(
    kernel: &mut Kernel,
    source: NameId,
    before: ExprId,
    after: ExprId,
) -> Result<CheckedSourceDeltaStep, SourceDeltaStepError> {
    let value = definition_value(kernel, source)?;
    let (head, arguments) = unfold_apps(kernel, before);
    let ExprNode::Const(observed_source, levels) = kernel.expr_node(head).clone() else {
        return Err(SourceDeltaStepError::SourceHeadMismatch);
    };
    if observed_source != source {
        return Err(SourceDeltaStepError::SourceHeadMismatch);
    }
    let instantiated = instantiate_value(kernel, source, value, &levels)?;
    let mut expected_after = instantiated;
    for &argument in &arguments {
        expected_after = kernel.app(expected_after, argument);
    }
    if after != expected_after {
        return Err(SourceDeltaStepError::AfterMismatch);
    }
    let source_content_sha256 =
        canonical_declaration_sha256(kernel, source).map_err(SourceDeltaStepError::Identity)?;
    Ok(CheckedSourceDeltaStep {
        source,
        source_content_sha256,
        levels,
        arguments,
        before,
        after,
    })
}

fn definition_value(kernel: &Kernel, source: NameId) -> Result<ExprId, SourceDeltaStepError> {
    match kernel.environment().get(source) {
        Some(Declaration::Definition { value, .. }) => Ok(*value),
        _ => Err(SourceDeltaStepError::SourceNotDefinition),
    }
}

fn instantiate_value(
    kernel: &mut Kernel,
    source: NameId,
    value: ExprId,
    levels: &[LevelId],
) -> Result<ExprId, SourceDeltaStepError> {
    let uparams = kernel
        .environment()
        .get(source)
        .ok_or(SourceDeltaStepError::SourceNotDefinition)?
        .uparams()
        .to_vec();
    if uparams.len() != levels.len() {
        return Err(SourceDeltaStepError::UniverseArityMismatch {
            expected: uparams.len(),
            observed: levels.len(),
        });
    }
    let substitution: Vec<_> = uparams.into_iter().zip(levels.iter().copied()).collect();
    Ok(kernel.substitute_expr_levels(value, &substitution))
}

fn unfold_apps(kernel: &Kernel, mut expression: ExprId) -> (ExprId, Vec<ExprId>) {
    let mut arguments = Vec::new();
    while let ExprNode::App(function, argument) = kernel.expr_node(expression) {
        arguments.push(*argument);
        expression = *function;
    }
    arguments.reverse();
    (expression, arguments)
}
