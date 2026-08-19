//! Checked constant generalization for proof-free statement type slices.
//!
//! This module implements ADR-0484's semantic middle step. Selection policy is
//! intentionally separate: callers supply an ordered list of exact constant
//! instances. This code verifies that list, replaces those constants by local
//! parameters, closes the telescope, and asks the independent kernel to check
//! the resulting proposition.

use std::collections::{BTreeMap, HashMap};
use std::fmt;

use axeyum_lean_kernel::Declaration;
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
    /// Automatic v1 selection encountered a trusted declaration directly in a
    /// proposition-facing type.
    TrustedTypeDependency {
        /// Rendered declaration name.
        name: String,
        /// Stable declaration kind.
        kind: &'static str,
    },
    /// Automatic v1 selection encountered a missing declaration.
    MissingTypeDependency {
        /// Rendered declaration name.
        name: String,
    },
    /// Definition-type dependencies formed a cycle and cannot become a `Pi`
    /// telescope.
    AbstractionDependencyCycle {
        /// Rendered declaration at the detected cycle.
        name: String,
    },
    /// V1 cannot infer the universe instance of a definition named only by a
    /// projection's structure-type metadata.
    DefinitionProjectionType {
        /// Rendered projection structure type.
        name: String,
    },
    /// The exact atomic closure of a retained inductive-layer declaration would
    /// expose a trusted declaration to the producer.
    TrustedRetainedClosure {
        /// Retained declaration requested by the proposition.
        declaration: String,
        /// Trusted declaration pulled by its atomic closure.
        dependency: String,
        /// Stable trusted declaration kind.
        kind: &'static str,
    },
    /// Exact atomic root-closure construction failed during selection.
    RootClosure {
        /// Declaration whose closure was requested.
        name: String,
        /// Exporter's fail-closed diagnostic.
        reason: String,
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
            Self::TrustedTypeDependency { name, kind } => {
                write!(f, "type boundary directly references {kind} {name}")
            }
            Self::MissingTypeDependency { name } => {
                write!(f, "type boundary references missing declaration {name}")
            }
            Self::AbstractionDependencyCycle { name } => {
                write!(f, "definition abstraction dependency cycles at {name}")
            }
            Self::DefinitionProjectionType { name } => write!(
                f,
                "projection structure type {name} is a definition unsupported by v1 selection"
            ),
            Self::TrustedRetainedClosure {
                declaration,
                dependency,
                kind,
            } => write!(
                f,
                "retaining {declaration} would expose {kind} {dependency}"
            ),
            Self::RootClosure { name, reason } => {
                write!(f, "cannot construct atomic closure for {name}: {reason}")
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

#[derive(Clone, Copy)]
enum ClosureNormalization {
    Exact,
    AutoParamTypes,
    AutoParamBinders,
}

/// Conservatively select each ordinary definition instance whose complete
/// implementation closure contains a trusted declaration and is reachable from
/// a proposition or another selected instance's type, in dependency-first
/// order. Definitions with wholly proof-free implementation closure remain
/// concrete so required definitional equality is preserved.
///
/// Inductives, constructors, and recursors remain concrete so their computation
/// rules survive root-selected transport. A direct axiom, theorem, opaque, or
/// quotient dependency declines rather than becoming an implicit premise.
/// Definition-backed projection structure types also decline because projection
/// metadata does not carry the universe instance needed for an exact key.
///
/// # Errors
///
/// Returns [`TypeSliceError`] for trusted/missing direct dependencies,
/// definition-type cycles, unsupported projection types, or kernel inference
/// failure.
pub fn select_definition_abstractions_v1(
    kernel: &mut Kernel,
    goal: ExprId,
) -> Result<Vec<ConstantInstance>, TypeSliceError> {
    select_definition_abstractions(kernel, goal, ClosureNormalization::Exact)
}

/// Apply v1 selection after checked type-only normalization of canonical
/// `autoParam` annotations in every retained atomic closure.
///
/// # Errors
///
/// Returns the v1 selection errors or a typed root-normalization diagnostic.
pub fn select_definition_abstractions_auto_param_v2(
    kernel: &mut Kernel,
    goal: ExprId,
) -> Result<Vec<ConstantInstance>, TypeSliceError> {
    select_definition_abstractions(kernel, goal, ClosureNormalization::AutoParamTypes)
}

/// Apply v1 selection after checked normalization of canonical `autoParam`
/// annotations in declaration types and recursor-rule binder domains.
///
/// # Errors
///
/// Returns the v1 selection errors or a typed binder-normalization diagnostic.
pub fn select_definition_abstractions_auto_param_binders_v3(
    kernel: &mut Kernel,
    goal: ExprId,
) -> Result<Vec<ConstantInstance>, TypeSliceError> {
    select_definition_abstractions(kernel, goal, ClosureNormalization::AutoParamBinders)
}

fn select_definition_abstractions(
    kernel: &mut Kernel,
    goal: ExprId,
    normalization: ClosureNormalization,
) -> Result<Vec<ConstantInstance>, TypeSliceError> {
    ensure_closed(kernel, goal, "source goal")?;
    ensure_prop(kernel, goal, "source goal")?;
    let mut states = BTreeMap::new();
    let mut trusted_closure_by_name = BTreeMap::new();
    let mut ordered = Vec::new();
    select_from_expression(
        kernel,
        goal,
        &mut states,
        &mut trusted_closure_by_name,
        &mut ordered,
        normalization,
    )?;
    Ok(ordered
        .into_iter()
        .map(|(name, levels)| ConstantInstance {
            name,
            levels,
            binder_name: name,
        })
        .collect())
}

fn select_from_expression(
    kernel: &mut Kernel,
    expression: ExprId,
    states: &mut BTreeMap<InstanceKey, u8>,
    trusted_closure_by_name: &mut BTreeMap<NameId, Option<(NameId, &'static str)>>,
    ordered: &mut Vec<InstanceKey>,
    normalization: ClosureNormalization,
) -> Result<(), TypeSliceError> {
    match kernel.expr_node(expression).clone() {
        ExprNode::Const(name, levels) => {
            select_constant_instance(
                kernel,
                name,
                levels,
                states,
                trusted_closure_by_name,
                ordered,
                normalization,
            )?;
        }
        ExprNode::Proj(type_name, _, structure) => {
            let kind = declaration_selection_kind(
                kernel,
                type_name,
                trusted_closure_by_name,
                normalization,
            )?;
            match kind {
                SelectionKind::Definition => {
                    return Err(TypeSliceError::DefinitionProjectionType {
                        name: kernel.display_name(type_name).to_string(),
                    });
                }
                SelectionKind::Trusted(kind) => {
                    return Err(TypeSliceError::TrustedTypeDependency {
                        name: kernel.display_name(type_name).to_string(),
                        kind,
                    });
                }
                SelectionKind::Retain => {}
            }
            select_from_expression(
                kernel,
                structure,
                states,
                trusted_closure_by_name,
                ordered,
                normalization,
            )?;
        }
        ExprNode::App(function, argument)
        | ExprNode::Lam(_, function, argument, _)
        | ExprNode::Pi(_, function, argument, _) => {
            select_from_expression(
                kernel,
                function,
                states,
                trusted_closure_by_name,
                ordered,
                normalization,
            )?;
            select_from_expression(
                kernel,
                argument,
                states,
                trusted_closure_by_name,
                ordered,
                normalization,
            )?;
        }
        ExprNode::Let(_, ty, value, body) => {
            for child in [ty, value, body] {
                select_from_expression(
                    kernel,
                    child,
                    states,
                    trusted_closure_by_name,
                    ordered,
                    normalization,
                )?;
            }
        }
        ExprNode::BVar(_) | ExprNode::FVar(_) | ExprNode::Sort(_) | ExprNode::Lit(_) => {}
    }
    Ok(())
}

fn select_constant_instance(
    kernel: &mut Kernel,
    name: NameId,
    levels: Vec<LevelId>,
    states: &mut BTreeMap<InstanceKey, u8>,
    trusted_closure_by_name: &mut BTreeMap<NameId, Option<(NameId, &'static str)>>,
    ordered: &mut Vec<InstanceKey>,
    normalization: ClosureNormalization,
) -> Result<(), TypeSliceError> {
    match declaration_selection_kind(kernel, name, trusted_closure_by_name, normalization)? {
        SelectionKind::Retain => Ok(()),
        SelectionKind::Trusted(kind) => Err(TypeSliceError::TrustedTypeDependency {
            name: kernel.display_name(name).to_string(),
            kind,
        }),
        SelectionKind::Definition => {
            let key = (name, levels);
            match states.get(&key) {
                Some(2) => return Ok(()),
                Some(1) => {
                    return Err(TypeSliceError::AbstractionDependencyCycle {
                        name: kernel.display_name(name).to_string(),
                    });
                }
                _ => {}
            }
            states.insert(key.clone(), 1);
            let constant = kernel.const_(key.0, key.1.clone());
            let ty = kernel
                .infer(constant)
                .map_err(|source| TypeSliceError::Kernel {
                    stage: "selection constant type inference",
                    source,
                })?;
            select_from_expression(
                kernel,
                ty,
                states,
                trusted_closure_by_name,
                ordered,
                normalization,
            )?;
            states.insert(key.clone(), 2);
            ordered.push(key);
            Ok(())
        }
    }
}

#[derive(Clone, Copy)]
enum SelectionKind {
    Retain,
    Definition,
    Trusted(&'static str),
}

fn declaration_selection_kind(
    kernel: &mut Kernel,
    name: NameId,
    trusted_closure_by_name: &mut BTreeMap<NameId, Option<(NameId, &'static str)>>,
    normalization: ClosureNormalization,
) -> Result<SelectionKind, TypeSliceError> {
    let Some(declaration) = kernel.environment().get(name) else {
        return Err(TypeSliceError::MissingTypeDependency {
            name: kernel.display_name(name).to_string(),
        });
    };
    Ok(match declaration {
        Declaration::Definition { .. } => {
            if trusted_atomic_dependency(kernel, name, trusted_closure_by_name, normalization)?
                .is_some()
            {
                SelectionKind::Definition
            } else {
                SelectionKind::Retain
            }
        }
        Declaration::Axiom { .. } => SelectionKind::Trusted("axiom"),
        Declaration::Theorem { .. } => SelectionKind::Trusted("theorem"),
        Declaration::Opaque { .. } => SelectionKind::Trusted("opaque"),
        Declaration::Quotient { .. } => SelectionKind::Trusted("quotient"),
        Declaration::Inductive { .. }
        | Declaration::Constructor { .. }
        | Declaration::Recursor { .. } => {
            if let Some((dependency, kind)) =
                trusted_atomic_dependency(kernel, name, trusted_closure_by_name, normalization)?
            {
                return Err(TypeSliceError::TrustedRetainedClosure {
                    declaration: kernel.display_name(name).to_string(),
                    dependency: kernel.display_name(dependency).to_string(),
                    kind,
                });
            }
            SelectionKind::Retain
        }
    })
}

fn trusted_atomic_dependency(
    kernel: &mut Kernel,
    name: NameId,
    cache: &mut BTreeMap<NameId, Option<(NameId, &'static str)>>,
    normalization: ClosureNormalization,
) -> Result<Option<(NameId, &'static str)>, TypeSliceError> {
    if let Some(result) = cache.get(&name) {
        return Ok(*result);
    }
    let closure = match normalization {
        ClosureNormalization::Exact => kernel.root_declaration_closure(&[name]),
        ClosureNormalization::AutoParamTypes => kernel
            .root_declaration_closure_checked_auto_param_types(&[name])
            .map(|(closure, _)| closure),
        ClosureNormalization::AutoParamBinders => kernel
            .root_declaration_closure_checked_auto_param_binders(&[name])
            .map(|(closure, _)| closure),
    }
    .map_err(|error| TypeSliceError::RootClosure {
        name: kernel.display_name(name).to_string(),
        reason: error.to_string(),
    })?;
    let result = closure.into_iter().find_map(|dependency| {
        let kind = match kernel.environment().get(dependency) {
            Some(Declaration::Axiom { .. }) => "axiom",
            Some(Declaration::Theorem { .. }) => "theorem",
            Some(Declaration::Opaque { .. }) => "opaque",
            Some(Declaration::Quotient { .. }) => "quotient",
            _ => return None,
        };
        Some((dependency, kind))
    });
    cache.insert(name, result);
    Ok(result)
}

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
