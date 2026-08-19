//! Checked residualization of transparent function bodies into local contracts.

use std::collections::{BTreeMap, BTreeSet, HashSet};
use std::fmt;

use axeyum_lean_kernel::{Declaration, ExprId, ExprNode, Kernel, LevelId, NameId};

use crate::{
    ConstantInstance, GeneralizedGoal, TypeSliceError, generalize_goal_constants,
    verify_generalized_specialization,
};

type InstanceKey = (NameId, Vec<LevelId>);

/// One pointwise transparent equation whose omitted body constants have become
/// exact ordered local parameters.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ResidualizedFunctionContract {
    /// Closed concrete equation before source/dependency generalization.
    pub source_equation: ExprId,
    /// Producer-facing equation with source and residual constants generalized.
    pub generalized: GeneralizedGoal,
    /// Exact source constants that independently specialize the telescope.
    pub source_arguments: Vec<ExprId>,
    /// Number of pointwise arguments exposed by the source function type.
    pub function_arity: usize,
}

/// Contract-body residualization failed closed.
#[derive(Debug)]
pub enum ResidualizedFunctionContractError {
    /// The selected source was not a transparent definition.
    SourceNotDefinition,
    /// Version 1 accepts only monomorphic source definitions.
    PolymorphicSource,
    /// The source type exposed no ordinary function binder.
    SourceNotFunction,
    /// Dependent result types are deferred until the first nondependent control
    /// establishes the boundary.
    DependentResultUnsupported,
    /// A projection body requires exact projection-universe accounting not yet
    /// represented by `ConstantInstance`.
    ProjectionBodyUnsupported,
    /// One direct body constant was neither self, retained, nor residualized.
    UnaccountedBodyConstant {
        /// Exact rendered declaration name.
        name: String,
    },
    /// An exact constant instance appeared in multiple authority classes.
    DuplicateAuthority {
        /// Exact rendered declaration name.
        name: String,
    },
    /// Canonical `Eq` was absent or ambiguous.
    EqualityIdentity {
        /// Number of rendered `Eq` declarations found.
        observed: usize,
    },
    /// The result type did not independently inhabit a sort.
    ResultNotSort,
    /// Existing checked type-slice generalization or specialization failed.
    Slice(TypeSliceError),
    /// The independent kernel rejected a constructed expression.
    Kernel {
        /// Stable construction stage.
        stage: &'static str,
        /// Kernel diagnostic.
        source: axeyum_lean_kernel::KernelError,
    },
}

impl fmt::Display for ResidualizedFunctionContractError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::SourceNotDefinition => write!(formatter, "contract source is not a definition"),
            Self::PolymorphicSource => write!(formatter, "contract source is polymorphic"),
            Self::SourceNotFunction => write!(formatter, "contract source is not a function"),
            Self::DependentResultUnsupported => {
                write!(
                    formatter,
                    "dependent contract result is not supported by v1"
                )
            }
            Self::ProjectionBodyUnsupported => {
                write!(formatter, "projection body is not supported by v1")
            }
            Self::UnaccountedBodyConstant { name } => {
                write!(formatter, "contract body constant {name} is unaccounted")
            }
            Self::DuplicateAuthority { name } => {
                write!(
                    formatter,
                    "contract constant {name} has duplicate authority"
                )
            }
            Self::EqualityIdentity { observed } => {
                write!(formatter, "canonical Eq occurs {observed} times")
            }
            Self::ResultNotSort => write!(formatter, "contract result type is not a sort"),
            Self::Slice(error) => write!(formatter, "contract type slice failed: {error}"),
            Self::Kernel { stage, source } => {
                write!(formatter, "contract {stage} failed: {source:?}")
            }
        }
    }
}

impl std::error::Error for ResidualizedFunctionContractError {}

impl From<TypeSliceError> for ResidualizedFunctionContractError {
    fn from(error: TypeSliceError) -> Self {
        Self::Slice(error)
    }
}

/// Build and source-specialize a pointwise equation with explicit residual body
/// dependencies.
///
/// `source` is always binder zero. `residual` follows in dependency order and
/// becomes producer-visible local parameters. `retained` identifies exact
/// direct body instances already admitted to the proof-free environment. Every
/// direct constant in the transparent value must fall in exactly one of those
/// classes; recursive self-occurrences reuse the source binder.
///
/// Version 1 deliberately accepts only monomorphic functions with a
/// nondependent result and no projections. Those are explicit declines, not
/// silent approximations.
///
/// # Errors
///
/// Returns [`ResidualizedFunctionContractError`] on authority overlap,
/// unaccounted body closure, unsupported source shape, or any failed kernel,
/// generalization, or specialization check.
#[allow(clippy::too_many_lines)]
pub fn residualize_function_contract_body(
    kernel: &mut Kernel,
    source: &ConstantInstance,
    residual: &[ConstantInstance],
    retained: &[ConstantInstance],
) -> Result<ResidualizedFunctionContract, ResidualizedFunctionContractError> {
    let (source_type, source_value, source_uparams) = match kernel.environment().get(source.name) {
        Some(Declaration::Definition {
            ty, value, uparams, ..
        }) => (*ty, *value, uparams.clone()),
        _ => return Err(ResidualizedFunctionContractError::SourceNotDefinition),
    };
    if !source_uparams.is_empty() || !source.levels.is_empty() {
        return Err(ResidualizedFunctionContractError::PolymorphicSource);
    }

    let source_key = (source.name, source.levels.clone());
    let mut authority = BTreeMap::<InstanceKey, &'static str>::new();
    authority.insert(source_key.clone(), "source");
    for (class, instances) in [("residual", residual), ("retained", retained)] {
        for instance in instances {
            let key = (instance.name, instance.levels.clone());
            if authority.insert(key, class).is_some() {
                return Err(ResidualizedFunctionContractError::DuplicateAuthority {
                    name: kernel.display_name(instance.name).to_string(),
                });
            }
        }
    }
    for key in direct_instances(kernel, source_value)? {
        if !authority.contains_key(&key) {
            return Err(ResidualizedFunctionContractError::UnaccountedBodyConstant {
                name: kernel.display_name(key.0).to_string(),
            });
        }
    }

    let mut current_type = source_type;
    let source_term = kernel.const_(source.name, source.levels.clone());
    let mut source_application = source_term;
    let mut value_application = source_value;
    let mut arguments = Vec::new();
    while let ExprNode::Pi(name, domain, body, info) = kernel.expr_node(current_type).clone() {
        let fvar = u64::MAX - 10_000 - u64::try_from(arguments.len()).unwrap_or(u64::MAX / 2);
        let argument = kernel.fvar(fvar);
        source_application = kernel.app(source_application, argument);
        value_application = kernel.app(value_application, argument);
        current_type = kernel.instantiate(body, &[argument]);
        arguments.push((name, domain, info, fvar));
    }
    if arguments.is_empty() {
        return Err(ResidualizedFunctionContractError::SourceNotFunction);
    }
    if kernel.has_fvars(current_type) {
        return Err(ResidualizedFunctionContractError::DependentResultUnsupported);
    }
    let result_sort =
        kernel
            .infer(current_type)
            .map_err(|source| ResidualizedFunctionContractError::Kernel {
                stage: "result sort inference",
                source,
            })?;
    let result_sort = kernel.whnf(result_sort);
    let ExprNode::Sort(result_level) = *kernel.expr_node(result_sort) else {
        return Err(ResidualizedFunctionContractError::ResultNotSort);
    };
    let equality_names: Vec<_> = kernel
        .environment()
        .iter()
        .filter_map(|(&name, _)| (kernel.display_name(name).to_string() == "Eq").then_some(name))
        .collect();
    let [equality] = equality_names.as_slice() else {
        return Err(ResidualizedFunctionContractError::EqualityIdentity {
            observed: equality_names.len(),
        });
    };
    let equality = kernel.const_(*equality, vec![result_level]);
    let equality = kernel.app(equality, current_type);
    let equality = kernel.app(equality, source_application);
    let mut source_equation = kernel.app(equality, value_application);
    for (name, domain, info, fvar) in arguments.iter().rev() {
        source_equation = kernel.abstract_fvars(source_equation, &[*fvar]);
        source_equation = kernel.pi(*name, *domain, source_equation, *info);
    }

    let mut abstractions = Vec::with_capacity(1 + residual.len());
    abstractions.push(source.clone());
    abstractions.extend_from_slice(residual);
    let generalized = generalize_goal_constants(kernel, source_equation, &abstractions)?;
    let source_arguments: Vec<_> = abstractions
        .iter()
        .map(|instance| kernel.const_(instance.name, instance.levels.clone()))
        .collect();
    verify_generalized_specialization(kernel, &generalized, &source_arguments, source_equation)?;
    Ok(ResidualizedFunctionContract {
        source_equation,
        generalized,
        source_arguments,
        function_arity: arguments.len(),
    })
}

fn direct_instances(
    kernel: &Kernel,
    root: ExprId,
) -> Result<BTreeSet<InstanceKey>, ResidualizedFunctionContractError> {
    let mut output = BTreeSet::new();
    let mut seen = HashSet::new();
    let mut pending = vec![root];
    while let Some(expression) = pending.pop() {
        if !seen.insert(expression) {
            continue;
        }
        match kernel.expr_node(expression) {
            ExprNode::Const(name, levels) => {
                output.insert((*name, levels.clone()));
            }
            ExprNode::Proj(..) => {
                return Err(ResidualizedFunctionContractError::ProjectionBodyUnsupported);
            }
            ExprNode::App(function, argument)
            | ExprNode::Lam(_, function, argument, _)
            | ExprNode::Pi(_, function, argument, _) => {
                pending.extend([*function, *argument]);
            }
            ExprNode::Let(_, ty, value, body) => pending.extend([*ty, *value, *body]),
            ExprNode::BVar(_) | ExprNode::FVar(_) | ExprNode::Sort(_) | ExprNode::Lit(_) => {}
        }
    }
    Ok(output)
}
