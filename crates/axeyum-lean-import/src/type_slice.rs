//! Checked constant generalization for proof-free statement type slices.
//!
//! This module implements ADR-0484's semantic middle step. Selection policy is
//! intentionally separate: callers supply an ordered list of exact constant
//! instances. This code verifies that list, replaces those constants by local
//! parameters, closes the telescope, and asks the independent kernel to check
//! the resulting proposition.

use std::collections::{BTreeMap, HashMap};
use std::fmt;

use axeyum_lean_kernel::{BinderInfo, ExprId, ExprNode, Kernel, KernelError, LevelId, NameId};

/// One exact global constant instance to generalize.
///
/// Universe arguments are part of the key: two uses of the same declaration at
/// distinct instances are distinct parameters. `binder_name` is nonsemantic
/// display metadata for the generated `Pi`.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct ConstantInstance {
    /// Source declaration name in the supplied kernel.
    pub name: NameId,
    /// Exact universe arguments at this occurrence class.
    pub levels: Vec<LevelId>,
    /// Display name for the new explicit binder.
    pub binder_name: NameId,
}

/// One checked binder in a generalized goal.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GeneralizedBinder {
    /// The exact source constant instance replaced by this binder.
    pub source: ConstantInstance,
    /// Its independently inferred, recursively generalized type.
    pub ty: ExprId,
}

/// A closed proposition generalized over explicit non-proof parameters.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GeneralizedGoal {
    /// The closed `Pi` telescope ending in the transformed source goal.
    pub goal: ExprId,
    /// Binders in outer-to-inner order.
    pub binders: Vec<GeneralizedBinder>,
}

/// A supplied abstraction list or resulting proposition violated ADR-0484.
#[derive(Debug)]
pub enum TypeSliceError {
    /// The source goal or an inferred binder type was not closed.
    OpenExpression {
        /// Which expression failed the closure check.
        stage: String,
    },
    /// The source or generalized expression did not independently infer to `Prop`.
    GoalNotProp {
        /// Which goal failed.
        stage: &'static str,
    },
    /// Two entries named the same declaration at the same universe instance.
    DuplicateInstance {
        /// Rendered declaration name.
        name: String,
    },
    /// A requested instance did not occur in the goal or a later binder type.
    MissingOccurrence {
        /// Rendered declaration name.
        name: String,
    },
    /// The constant's instantiated type is itself a proposition, so the
    /// constant is a proof/premise rather than a data or function parameter.
    PropositionValued {
        /// Rendered declaration name.
        name: String,
    },
    /// A binder type references itself or a later abstraction, so the supplied
    /// order cannot form a dependent telescope.
    ForwardDependency {
        /// Binder whose type contains the reference.
        binder: String,
        /// Self/later constant referenced by that type.
        dependency: String,
    },
    /// A projection names an abstracted structure type. V1 cannot preserve its
    /// field semantics by replacing only ordinary `Const` nodes.
    AbstractedProjectionType {
        /// Rendered structure type name.
        name: String,
    },
    /// Exact specialization supplied the wrong number of arguments.
    SpecializationArity {
        /// Number of generalized binders.
        expected: usize,
        /// Number of supplied arguments.
        observed: usize,
    },
    /// A purported generalized goal did not expose the expected `Pi` binder.
    SpecializationNotPi {
        /// Zero-based argument position.
        index: usize,
    },
    /// A specialization argument did not have the current dependent binder type.
    SpecializationArgumentMismatch {
        /// Zero-based argument position.
        index: usize,
    },
    /// Applying every argument did not recover the expected source proposition.
    SpecializationMismatch,
    /// The independent kernel refused an inference or equality check.
    Kernel {
        /// Stable operation stage.
        stage: &'static str,
        /// Kernel diagnostic.
        source: KernelError,
    },
}

impl fmt::Display for TypeSliceError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::OpenExpression { stage } => write!(f, "{stage} contains free or loose variables"),
            Self::GoalNotProp { stage } => write!(f, "{stage} does not infer to Prop"),
            Self::DuplicateInstance { name } => {
                write!(f, "constant instance {name} is listed more than once")
            }
            Self::MissingOccurrence { name } => {
                write!(f, "constant instance {name} does not occur in the slice")
            }
            Self::PropositionValued { name } => {
                write!(f, "constant instance {name} has a proposition-valued type")
            }
            Self::ForwardDependency { binder, dependency } => write!(
                f,
                "binder {binder} depends on self/later abstraction {dependency}"
            ),
            Self::AbstractedProjectionType { name } => {
                write!(
                    f,
                    "projection structure type {name} cannot be abstracted in v1"
                )
            }
            Self::SpecializationArity { expected, observed } => write!(
                f,
                "specialization expected {expected} arguments but received {observed}"
            ),
            Self::SpecializationNotPi { index } => {
                write!(f, "generalized goal has no Pi at argument {index}")
            }
            Self::SpecializationArgumentMismatch { index } => {
                write!(f, "specialization argument {index} has the wrong type")
            }
            Self::SpecializationMismatch => {
                write!(f, "specialized goal does not equal the source proposition")
            }
            Self::Kernel { stage, source } => {
                write!(f, "kernel rejected {stage}: {source:?}")
            }
        }
    }
}

impl std::error::Error for TypeSliceError {}

type InstanceKey = (NameId, Vec<LevelId>);

/// Generalize exact global constant instances into an explicit dependent
/// `Pi` telescope and independently check the closed result as `Prop`.
///
/// `abstractions` must be dependency-ordered: if the type of entry `i`
/// references another listed instance, that dependency must occur before `i`.
/// The function rejects proof-valued constants, unused entries, abstracted
/// projection type names, duplicate instances, and open or ill-typed input.
///
/// This function does not choose which declarations are safe to retain or
/// abstract, does not create a fresh kernel, and does not prove specialization.
/// Those are separate ADR-0484 stages.
///
/// # Errors
///
/// Returns [`TypeSliceError`] for every contract violation or independent
/// kernel failure.
pub fn generalize_goal_constants(
    kernel: &mut Kernel,
    goal: ExprId,
    abstractions: &[ConstantInstance],
) -> Result<GeneralizedGoal, TypeSliceError> {
    ensure_closed(kernel, goal, "source goal")?;
    ensure_prop(kernel, goal, "source goal")?;

    let mut positions = BTreeMap::new();
    for (index, abstraction) in abstractions.iter().enumerate() {
        let key = (abstraction.name, abstraction.levels.clone());
        if positions.insert(key, index).is_some() {
            return Err(TypeSliceError::DuplicateInstance {
                name: kernel.display_name(abstraction.name).to_string(),
            });
        }
    }
    let fvars: Vec<u64> = (0_u64..)
        .take(abstractions.len())
        .map(|index| u64::MAX - index)
        .collect();
    let mut seen = vec![false; abstractions.len()];
    let mut binder_types = Vec::with_capacity(abstractions.len());
    for (index, abstraction) in abstractions.iter().enumerate() {
        let constant = kernel.const_(abstraction.name, abstraction.levels.clone());
        let ty = kernel
            .infer(constant)
            .map_err(|source| TypeSliceError::Kernel {
                stage: "constant type inference",
                source,
            })?;
        ensure_closed(
            kernel,
            ty,
            &format!("type of {}", kernel.display_name(abstraction.name)),
        )?;
        let type_type = kernel.infer(ty).map_err(|source| TypeSliceError::Kernel {
            stage: "constant type sort inference",
            source,
        })?;
        let prop = kernel.sort_zero();
        if kernel.def_eq(type_type, prop) {
            return Err(TypeSliceError::PropositionValued {
                name: kernel.display_name(abstraction.name).to_string(),
            });
        }
        let transformed = replace_instances(
            kernel,
            ty,
            &positions,
            &fvars,
            index,
            &mut seen,
            Some(abstraction.name),
        )?;
        binder_types.push(transformed);
    }

    let mut body = replace_instances(
        kernel,
        goal,
        &positions,
        &fvars,
        abstractions.len(),
        &mut seen,
        None,
    )?;
    for (index, abstraction) in abstractions.iter().enumerate() {
        if !seen[index] {
            return Err(TypeSliceError::MissingOccurrence {
                name: kernel.display_name(abstraction.name).to_string(),
            });
        }
    }
    for index in (0..abstractions.len()).rev() {
        body = kernel.abstract_fvars(body, &[fvars[index]]);
        body = kernel.pi(
            abstractions[index].binder_name,
            binder_types[index],
            body,
            BinderInfo::Default,
        );
    }
    ensure_closed(kernel, body, "generalized goal")?;
    ensure_prop(kernel, body, "generalized goal")?;
    Ok(GeneralizedGoal {
        goal: body,
        binders: abstractions
            .iter()
            .cloned()
            .zip(binder_types)
            .map(|(source, ty)| GeneralizedBinder { source, ty })
            .collect(),
    })
}

/// Independently apply exact source arguments to a generalized telescope and
/// require the result to be definitionally equal to the expected source goal.
///
/// Argument checking is dependent: each accepted argument is instantiated into
/// the remaining telescope before the next binder type is checked.
///
/// # Errors
///
/// Returns [`TypeSliceError`] if either proposition is open or ill-typed, the
/// argument count or a dependent argument type is wrong, the telescope shape is
/// inconsistent with its binder inventory, or specialization does not recover
/// `expected` exactly.
pub fn verify_generalized_specialization(
    kernel: &mut Kernel,
    generalized: &GeneralizedGoal,
    arguments: &[ExprId],
    expected: ExprId,
) -> Result<(), TypeSliceError> {
    ensure_closed(kernel, generalized.goal, "generalized goal")?;
    ensure_prop(kernel, generalized.goal, "generalized goal")?;
    ensure_closed(kernel, expected, "expected source goal")?;
    ensure_prop(kernel, expected, "expected source goal")?;
    if arguments.len() != generalized.binders.len() {
        return Err(TypeSliceError::SpecializationArity {
            expected: generalized.binders.len(),
            observed: arguments.len(),
        });
    }

    let mut current = generalized.goal;
    for (index, &argument) in arguments.iter().enumerate() {
        ensure_closed(
            kernel,
            argument,
            &format!("specialization argument {index}"),
        )?;
        let ExprNode::Pi(_, binder_ty, body, _) = kernel.expr_node(current).clone() else {
            return Err(TypeSliceError::SpecializationNotPi { index });
        };
        let argument_ty = kernel
            .infer(argument)
            .map_err(|source| TypeSliceError::Kernel {
                stage: "specialization argument inference",
                source,
            })?;
        if !kernel.def_eq(argument_ty, binder_ty) {
            return Err(TypeSliceError::SpecializationArgumentMismatch { index });
        }
        current = kernel.instantiate(body, &[argument]);
    }
    if kernel.def_eq(current, expected) {
        Ok(())
    } else {
        Err(TypeSliceError::SpecializationMismatch)
    }
}

fn ensure_closed(kernel: &Kernel, expression: ExprId, stage: &str) -> Result<(), TypeSliceError> {
    if kernel.has_fvars(expression) || kernel.has_loose_bvars(expression) {
        Err(TypeSliceError::OpenExpression {
            stage: stage.to_owned(),
        })
    } else {
        Ok(())
    }
}

fn ensure_prop(
    kernel: &mut Kernel,
    expression: ExprId,
    stage: &'static str,
) -> Result<(), TypeSliceError> {
    let inferred = kernel
        .infer(expression)
        .map_err(|source| TypeSliceError::Kernel { stage, source })?;
    let prop = kernel.sort_zero();
    if kernel.def_eq(inferred, prop) {
        Ok(())
    } else {
        Err(TypeSliceError::GoalNotProp { stage })
    }
}

#[allow(clippy::too_many_arguments)]
fn replace_instances(
    kernel: &mut Kernel,
    root: ExprId,
    positions: &BTreeMap<InstanceKey, usize>,
    fvars: &[u64],
    active: usize,
    seen: &mut [bool],
    binder: Option<NameId>,
) -> Result<ExprId, TypeSliceError> {
    let mut memo = HashMap::new();
    replace_instances_aux(
        kernel, root, positions, fvars, active, seen, binder, &mut memo,
    )
}

#[allow(clippy::too_many_arguments, clippy::too_many_lines)]
fn replace_instances_aux(
    kernel: &mut Kernel,
    expression: ExprId,
    positions: &BTreeMap<InstanceKey, usize>,
    fvars: &[u64],
    active: usize,
    seen: &mut [bool],
    binder: Option<NameId>,
    memo: &mut HashMap<ExprId, ExprId>,
) -> Result<ExprId, TypeSliceError> {
    if let Some(&transformed) = memo.get(&expression) {
        return Ok(transformed);
    }
    let transformed = match kernel.expr_node(expression).clone() {
        ExprNode::Const(name, levels) => {
            let key = (name, levels);
            if let Some(&index) = positions.get(&key) {
                if index >= active {
                    return Err(TypeSliceError::ForwardDependency {
                        binder: binder.map_or_else(
                            || "goal".to_owned(),
                            |id| kernel.display_name(id).to_string(),
                        ),
                        dependency: kernel.display_name(name).to_string(),
                    });
                }
                seen[index] = true;
                kernel.fvar(fvars[index])
            } else {
                expression
            }
        }
        ExprNode::Proj(type_name, field_index, structure) => {
            if positions.keys().any(|(name, _)| *name == type_name) {
                return Err(TypeSliceError::AbstractedProjectionType {
                    name: kernel.display_name(type_name).to_string(),
                });
            }
            let structure = replace_instances_aux(
                kernel, structure, positions, fvars, active, seen, binder, memo,
            )?;
            kernel.proj(type_name, field_index, structure)
        }
        ExprNode::App(function, argument) => {
            let function = replace_instances_aux(
                kernel, function, positions, fvars, active, seen, binder, memo,
            )?;
            let argument = replace_instances_aux(
                kernel, argument, positions, fvars, active, seen, binder, memo,
            )?;
            kernel.app(function, argument)
        }
        ExprNode::Lam(name, ty, body, info) => {
            let ty =
                replace_instances_aux(kernel, ty, positions, fvars, active, seen, binder, memo)?;
            let body =
                replace_instances_aux(kernel, body, positions, fvars, active, seen, binder, memo)?;
            kernel.lam(name, ty, body, info)
        }
        ExprNode::Pi(name, ty, body, info) => {
            let ty =
                replace_instances_aux(kernel, ty, positions, fvars, active, seen, binder, memo)?;
            let body =
                replace_instances_aux(kernel, body, positions, fvars, active, seen, binder, memo)?;
            kernel.pi(name, ty, body, info)
        }
        ExprNode::Let(name, ty, value, body) => {
            let ty =
                replace_instances_aux(kernel, ty, positions, fvars, active, seen, binder, memo)?;
            let value =
                replace_instances_aux(kernel, value, positions, fvars, active, seen, binder, memo)?;
            let body =
                replace_instances_aux(kernel, body, positions, fvars, active, seen, binder, memo)?;
            kernel.let_(name, ty, value, body)
        }
        ExprNode::BVar(_) | ExprNode::FVar(_) | ExprNode::Sort(_) | ExprNode::Lit(_) => expression,
    };
    memo.insert(expression, transformed);
    Ok(transformed)
}
