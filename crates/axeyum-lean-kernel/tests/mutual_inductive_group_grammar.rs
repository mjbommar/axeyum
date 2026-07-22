//! Independent fixed-seed grammar for TL2.13 M3 mutual inductive groups.
//!
//! Every case is constructed from a production record and enters through the
//! public [`Kernel::add_mutual_inductive`] gate. Positive expectations are
//! derived before observing the environment; negative expectations include an
//! exact typed error and complete environment rollback.
#![allow(clippy::too_many_arguments, clippy::too_many_lines)]

use std::cmp::Ordering;
use std::collections::{BTreeMap, BTreeSet};

use axeyum_lean_kernel::{
    BinderInfo, Declaration, ExprId, ExprNode, InductiveFamilySpec, Kernel, KernelError, NameId,
};

const GENERATOR_SEED: u64 = 0x4158_4D55_545F_4D33;
const EXPECTED_GENERATED_SUMMARY: &str = "schema=axeyum-lean-mutual-group-grammar-v1\n\
seed=41584d55545f4d33\n\
cases=720\n\
outcomes=admit:432,reject:288\n\
group-sizes=1:240,2:240,3:240\n\
parameter-profiles=0p:180,1p:180,2p-dependent:180,2p-independent:180\n\
sorts=prop:360,type:360\n\
productions=cross-earlier:72,cross-later:72,invalid-arity:72,invalid-parameter-or-index:72,mixed-self-cross:72,multiple-targets:72,negative-domain:72,no-recursion:72,result-mismatch:72,self-recursive:72\n\
primary-and-recursive-depths=0:240,1:240,2:240,recursive-0:192,recursive-1:192,recursive-2:192\n\
per-family-index-counts=0:485,1:481,2:474\n\
per-family-constructor-counts=0:235,1:132,2:689,3:384\n\
selected-total-fields=0:57,1:114,2:117,3:142,4:145,5:145\n\
selected-recursive-fields=0:360,1:216,2:72,3:72\n\
recursive-targets=earlier:124,later:116,self:336\n\
recursive-binder-info=Default:193,Implicit:193,StrictImplicit:190\n\
selected-index-productions=recursive-constant:426,recursive-field-dependent:175,result-constant:363,result-field-dependent:50\n\
mutation-checks=group-order:288,negative-rollback:288,target-family:240\n\
descriptor-fnv1a64=2ea6769fa45ea159\n";

#[derive(Clone, Copy, Debug)]
struct Lcg(u64);

impl Lcg {
    fn next_u64(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        self.0
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ParamProfile {
    P0,
    P1,
    P2Independent,
    P2Dependent,
}

impl ParamProfile {
    const ALL: [Self; 4] = [Self::P0, Self::P1, Self::P2Independent, Self::P2Dependent];

    const fn label(self) -> &'static str {
        match self {
            Self::P0 => "0p",
            Self::P1 => "1p",
            Self::P2Independent => "2p-independent",
            Self::P2Dependent => "2p-dependent",
        }
    }

    const fn count(self) -> usize {
        match self {
            Self::P0 => 0,
            Self::P1 => 1,
            Self::P2Independent | Self::P2Dependent => 2,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum FamilySort {
    Prop,
    Type,
}

impl FamilySort {
    const ALL: [Self; 2] = [Self::Prop, Self::Type];

    const fn label(self) -> &'static str {
        match self {
            Self::Prop => "prop",
            Self::Type => "type",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Production {
    NoRecursion,
    SelfRecursive,
    CrossEarlier,
    CrossLater,
    MixedSelfCross,
    MultipleTargets,
    NegativeDomain,
    InvalidArity,
    InvalidParameterOrIndex,
    ResultMismatch,
}

impl Production {
    const ALL: [Self; 10] = [
        Self::NoRecursion,
        Self::SelfRecursive,
        Self::CrossEarlier,
        Self::CrossLater,
        Self::MixedSelfCross,
        Self::MultipleTargets,
        Self::NegativeDomain,
        Self::InvalidArity,
        Self::InvalidParameterOrIndex,
        Self::ResultMismatch,
    ];

    const fn label(self) -> &'static str {
        match self {
            Self::NoRecursion => "no-recursion",
            Self::SelfRecursive => "self-recursive",
            Self::CrossEarlier => "cross-earlier",
            Self::CrossLater => "cross-later",
            Self::MixedSelfCross => "mixed-self-cross",
            Self::MultipleTargets => "multiple-targets",
            Self::NegativeDomain => "negative-domain",
            Self::InvalidArity => "invalid-arity",
            Self::InvalidParameterOrIndex => "invalid-parameter-or-index",
            Self::ResultMismatch => "result-mismatch",
        }
    }

    const fn is_positive(self) -> bool {
        matches!(
            self,
            Self::NoRecursion
                | Self::SelfRecursive
                | Self::CrossEarlier
                | Self::CrossLater
                | Self::MixedSelfCross
                | Self::MultipleTargets
        )
    }

    const fn recursive_fields(self) -> usize {
        match self {
            Self::SelfRecursive | Self::CrossEarlier | Self::CrossLater => 1,
            Self::MixedSelfCross => 2,
            Self::MultipleTargets => 3,
            Self::NoRecursion
            | Self::NegativeDomain
            | Self::InvalidArity
            | Self::InvalidParameterOrIndex
            | Self::ResultMismatch => 0,
        }
    }
}

#[derive(Clone, Debug)]
struct CaseSpec {
    id: String,
    ordinal: usize,
    group_size: usize,
    params: ParamProfile,
    family_sort: FamilySort,
    production: Production,
    primary_depth: usize,
    owner: usize,
    index_counts: Vec<usize>,
    constructor_counts: Vec<usize>,
    total_fields: usize,
    recursive_positions: Vec<usize>,
    recursive_targets: Vec<usize>,
    recursive_depths: Vec<usize>,
    binder_infos: Vec<BinderInfo>,
    field_dependent_indices: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct ExpectedContract {
    family_names: Vec<NameId>,
    constructor_names: Vec<Vec<NameId>>,
    constructor_field_counts: Vec<Vec<usize>>,
    index_counts: Vec<usize>,
    is_recursive: bool,
    motive_family_order: Vec<NameId>,
    minor_constructor_order: Vec<NameId>,
    rule_target_counts: Vec<Vec<Vec<usize>>>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum MutationClass {
    GroupOrder,
    TargetFamily,
    NegativeRollback,
}

impl MutationClass {
    const fn label(self) -> &'static str {
        match self {
            Self::GroupOrder => "group-order",
            Self::TargetFamily => "target-family",
            Self::NegativeRollback => "negative-rollback",
        }
    }
}

fn sort_one(kernel: &mut Kernel) -> ExprId {
    let zero = kernel.level_zero();
    let one = kernel.level_succ(zero);
    kernel.sort(one)
}

fn result_sort(kernel: &mut Kernel, family_sort: FamilySort) -> ExprId {
    match family_sort {
        FamilySort::Prop => kernel.sort_zero(),
        FamilySort::Type => sort_one(kernel),
    }
}

fn wrap_parameters(
    kernel: &mut Kernel,
    params: ParamProfile,
    binder: NameId,
    mut body: ExprId,
) -> ExprId {
    match params {
        ParamProfile::P0 => body,
        ParamProfile::P1 => {
            let domain = sort_one(kernel);
            kernel.pi(binder, domain, body, BinderInfo::Default)
        }
        ParamProfile::P2Independent => {
            let domain = sort_one(kernel);
            body = kernel.pi(binder, domain, body, BinderInfo::Implicit);
            let domain = sort_one(kernel);
            kernel.pi(binder, domain, body, BinderInfo::Default)
        }
        ParamProfile::P2Dependent => {
            let first_parameter = kernel.bvar(0);
            body = kernel.pi(binder, first_parameter, body, BinderInfo::StrictImplicit);
            let domain = sort_one(kernel);
            kernel.pi(binder, domain, body, BinderInfo::Default)
        }
    }
}

fn family_type(
    kernel: &mut Kernel,
    params: ParamProfile,
    indices: usize,
    family_sort: FamilySort,
    binder: NameId,
) -> ExprId {
    let mut ty = result_sort(kernel, family_sort);
    for index in (0..indices).rev() {
        let domain = sort_one(kernel);
        let info = if index % 2 == 0 {
            BinderInfo::Default
        } else {
            BinderInfo::Implicit
        };
        ty = kernel.pi(binder, domain, ty, info);
    }
    wrap_parameters(kernel, params, binder, ty)
}

fn parameter_values(
    kernel: &mut Kernel,
    params: ParamProfile,
    inner_binders: usize,
) -> Vec<ExprId> {
    let count = params.count();
    (0..count)
        .map(|parameter| {
            let depth = inner_binders + count - parameter - 1;
            kernel.bvar(u32::try_from(depth).expect("generated binder depth fits u32"))
        })
        .collect()
}

fn apply_family(
    kernel: &mut Kernel,
    family: ExprId,
    params: ParamProfile,
    inner_binders: usize,
    indices: &[ExprId],
) -> ExprId {
    let mut app = family;
    for parameter in parameter_values(kernel, params, inner_binders) {
        app = kernel.app(app, parameter);
    }
    for &index in indices {
        app = kernel.app(app, index);
    }
    app
}

fn constant_indices(kernel: &mut Kernel, count: usize) -> Vec<ExprId> {
    (0..count).map(|_| kernel.sort_zero()).collect()
}

fn recursive_indices(
    kernel: &mut Kernel,
    count: usize,
    preceding_fields: usize,
    telescope_depth: usize,
    field_dependent: bool,
) -> Vec<ExprId> {
    (0..count)
        .map(|index| {
            if field_dependent && telescope_depth > 0 && index == 0 {
                kernel.bvar(0)
            } else if field_dependent && preceding_fields > 0 && index == 0 {
                let depth = telescope_depth + preceding_fields - 1;
                kernel.bvar(u32::try_from(depth).expect("generated field depth fits u32"))
            } else {
                kernel.sort_zero()
            }
        })
        .collect()
}

fn recursive_field_type(
    kernel: &mut Kernel,
    family: ExprId,
    params: ParamProfile,
    index_count: usize,
    preceding_fields: usize,
    depth: usize,
    info: BinderInfo,
    field_dependent: bool,
    binder: NameId,
) -> ExprId {
    let indices = recursive_indices(
        kernel,
        index_count,
        preceding_fields,
        depth,
        field_dependent,
    );
    let mut tail = apply_family(kernel, family, params, preceding_fields + depth, &indices);
    for _ in 0..depth {
        let domain = sort_one(kernel);
        tail = kernel.pi(binder, domain, tail, info);
    }
    tail
}

fn result_indices(
    kernel: &mut Kernel,
    count: usize,
    total_fields: usize,
    field_dependent: bool,
) -> Vec<ExprId> {
    (0..count)
        .map(|index| {
            if field_dependent && total_fields > 0 && index == 0 {
                kernel
                    .bvar(u32::try_from(total_fields - 1).expect("generated field depth fits u32"))
            } else {
                kernel.sort_zero()
            }
        })
        .collect()
}

fn constructor_type(
    kernel: &mut Kernel,
    params: ParamProfile,
    owner: ExprId,
    owner_indices: usize,
    fields: &[(ExprId, BinderInfo)],
    field_dependent_result: bool,
    binder: NameId,
) -> ExprId {
    let indices = result_indices(kernel, owner_indices, fields.len(), field_dependent_result);
    let mut ty = apply_family(kernel, owner, params, fields.len(), &indices);
    for &(domain, info) in fields.iter().rev() {
        ty = kernel.pi(binder, domain, ty, info);
    }
    wrap_parameters(kernel, params, binder, ty)
}

fn base_constructor_type(
    kernel: &mut Kernel,
    params: ParamProfile,
    family: ExprId,
    indices: usize,
    binder: NameId,
) -> ExprId {
    constructor_type(kernel, params, family, indices, &[], false, binder)
}

fn effective_targets(spec: &CaseSpec) -> Vec<usize> {
    spec.recursive_targets.clone()
}

fn generate_specs() -> Vec<CaseSpec> {
    let mut rng = Lcg(GENERATOR_SEED);
    let mut specs = Vec::with_capacity(720);
    let mut ordinal = 0;
    for group_size in 1..=3 {
        for params in ParamProfile::ALL {
            for family_sort in FamilySort::ALL {
                for production in Production::ALL {
                    for primary_depth in 0..=2 {
                        let owner = usize::try_from(rng.next_u64()).unwrap() % group_size;
                        let index_counts = (0..group_size)
                            .map(|_| usize::try_from(rng.next_u64()).unwrap() % 3)
                            .collect::<Vec<_>>();
                        let mut constructor_counts = (0..group_size)
                            .map(|_| usize::try_from(rng.next_u64()).unwrap() % 4)
                            .collect::<Vec<_>>();
                        constructor_counts[owner] = constructor_counts[owner].max(2);

                        let recursive_count = production.recursive_fields();
                        let total_fields = if recursive_count == 0 {
                            usize::try_from(rng.next_u64()).unwrap() % 6
                        } else {
                            recursive_count
                                + (usize::try_from(rng.next_u64()).unwrap() % (6 - recursive_count))
                        };
                        let recursive_positions =
                            (total_fields.saturating_sub(recursive_count)..total_fields).collect();
                        let previous = owner.checked_sub(1).unwrap_or(group_size - 1);
                        let next = (owner + 1) % group_size;
                        let recursive_targets = match production {
                            Production::NoRecursion
                            | Production::NegativeDomain
                            | Production::InvalidArity
                            | Production::InvalidParameterOrIndex
                            | Production::ResultMismatch => Vec::new(),
                            Production::SelfRecursive => vec![owner],
                            Production::CrossEarlier => vec![previous],
                            Production::CrossLater => vec![next],
                            Production::MixedSelfCross => vec![owner, next],
                            Production::MultipleTargets => vec![owner, previous, next],
                        };
                        let recursive_depths = (0..recursive_count)
                            .map(|position| (primary_depth + position) % 3)
                            .collect::<Vec<_>>();
                        let binder_infos = (0..recursive_count)
                            .map(|_| match rng.next_u64() % 3 {
                                0 => BinderInfo::Default,
                                1 => BinderInfo::Implicit,
                                _ => BinderInfo::StrictImplicit,
                            })
                            .collect::<Vec<_>>();
                        let field_dependent_indices = rng.next_u64() & 1 == 1;
                        let id = format!(
                            "g{group_size}-{}-{}-{}-d{primary_depth}-o{ordinal:03}",
                            params.label(),
                            family_sort.label(),
                            production.label(),
                        );
                        specs.push(CaseSpec {
                            id,
                            ordinal,
                            group_size,
                            params,
                            family_sort,
                            production,
                            primary_depth,
                            owner,
                            index_counts,
                            constructor_counts,
                            total_fields,
                            recursive_positions,
                            recursive_targets,
                            recursive_depths,
                            binder_infos,
                            field_dependent_indices,
                        });
                        ordinal += 1;
                    }
                }
            }
        }
    }
    specs
}

fn count_constant(kernel: &Kernel, expression: ExprId, target: NameId) -> usize {
    match kernel.expr_node(expression).clone() {
        ExprNode::Const(name, _) => usize::from(name == target),
        ExprNode::BVar(_) | ExprNode::FVar(_) | ExprNode::Sort(_) | ExprNode::Lit(_) => 0,
        ExprNode::Proj(_, _, structure) => count_constant(kernel, structure, target),
        ExprNode::App(function, argument) => {
            count_constant(kernel, function, target) + count_constant(kernel, argument, target)
        }
        ExprNode::Lam(_, ty, body, _) | ExprNode::Pi(_, ty, body, _) => {
            count_constant(kernel, ty, target) + count_constant(kernel, body, target)
        }
        ExprNode::Let(_, ty, value, body) => {
            count_constant(kernel, ty, target)
                + count_constant(kernel, value, target)
                + count_constant(kernel, body, target)
        }
    }
}

fn pi_arity(kernel: &Kernel, mut expression: ExprId) -> usize {
    let mut arity = 0;
    while let ExprNode::Pi(_, _, body, _) = kernel.expr_node(expression).clone() {
        arity += 1;
        expression = body;
    }
    arity
}

fn ordered_constant_in(
    kernel: &Kernel,
    domain: ExprId,
    candidates: &[NameId],
    context: &str,
) -> NameId {
    let matches = candidates
        .iter()
        .copied()
        .filter(|&candidate| count_constant(kernel, domain, candidate) > 0)
        .collect::<Vec<_>>();
    assert_eq!(matches.len(), 1, "{context}: exactly one ordered constant");
    matches[0]
}

fn recursor_prefix_order(
    kernel: &Kernel,
    recursor_type: ExprId,
    num_params: usize,
    family_names: &[NameId],
    constructor_names: &[NameId],
) -> (Vec<NameId>, Vec<NameId>) {
    let mut cursor = recursor_type;
    for _ in 0..num_params {
        let ExprNode::Pi(_, _, body, _) = kernel.expr_node(cursor).clone() else {
            panic!("recursor parameter prefix must be a Pi telescope");
        };
        cursor = body;
    }
    let mut motives = Vec::with_capacity(family_names.len());
    for _ in family_names {
        let ExprNode::Pi(_, domain, body, _) = kernel.expr_node(cursor).clone() else {
            panic!("recursor motive prefix must be a Pi telescope");
        };
        motives.push(ordered_constant_in(kernel, domain, family_names, "motive"));
        cursor = body;
    }
    let mut minors = Vec::with_capacity(constructor_names.len());
    for _ in constructor_names {
        let ExprNode::Pi(_, domain, body, _) = kernel.expr_node(cursor).clone() else {
            panic!("recursor minor prefix must be a Pi telescope");
        };
        minors.push(ordered_constant_in(
            kernel,
            domain,
            constructor_names,
            "minor",
        ));
        cursor = body;
    }
    (motives, minors)
}

fn environment_snapshot(kernel: &Kernel) -> Vec<(NameId, Declaration)> {
    kernel
        .environment()
        .iter()
        .map(|(&name, declaration)| (name, declaration.clone()))
        .collect()
}

fn build_case(
    kernel: &mut Kernel,
    spec: &CaseSpec,
) -> (
    Vec<InductiveFamilySpec>,
    ExpectedContract,
    Vec<NameId>,
    Vec<NameId>,
) {
    let root = kernel.anon();
    let binder = kernel.name_str(root, "x");
    let family_names = (0..spec.group_size)
        .map(|family| kernel.name_str(root, format!("M3_{}_{family}", spec.ordinal)))
        .collect::<Vec<_>>();
    let family_constants = family_names
        .iter()
        .map(|&name| kernel.const_(name, vec![]))
        .collect::<Vec<_>>();
    let recursor_names = family_names
        .iter()
        .map(|&name| kernel.name_str(name, "rec"))
        .collect::<Vec<_>>();

    let mut families = Vec::with_capacity(spec.group_size);
    let mut constructor_names = Vec::with_capacity(spec.group_size);
    let mut constructor_field_counts = Vec::with_capacity(spec.group_size);
    let mut rule_target_counts = Vec::with_capacity(spec.group_size);
    let recursive_targets = effective_targets(spec);

    for family_index in 0..spec.group_size {
        let mut constructors = Vec::new();
        let mut names = Vec::new();
        let mut field_counts = Vec::new();
        let mut family_rule_targets = Vec::new();
        let desired = spec.constructor_counts[family_index];
        for constructor_index in 0..desired {
            let constructor =
                kernel.name_str(family_names[family_index], format!("c{constructor_index}"));
            let mut target_counts = vec![0; spec.group_size];
            let ty = if family_index == spec.owner && constructor_index == 1 {
                match spec.production {
                    Production::NegativeDomain => {
                        let target = (spec.owner + 1) % spec.group_size;
                        let indices = constant_indices(kernel, spec.index_counts[target]);
                        let occurrence = apply_family(
                            kernel,
                            family_constants[target],
                            spec.params,
                            0,
                            &indices,
                        );
                        let atom = kernel.sort_zero();
                        let negative = kernel.pi(binder, occurrence, atom, BinderInfo::Default);
                        constructor_type(
                            kernel,
                            spec.params,
                            family_constants[family_index],
                            spec.index_counts[family_index],
                            &[(negative, BinderInfo::Default)],
                            false,
                            binder,
                        )
                    }
                    Production::InvalidArity => {
                        let target = (spec.owner + 1) % spec.group_size;
                        let declared = spec.index_counts[target];
                        let supplied = if declared == 0 { 1 } else { declared - 1 };
                        let indices = constant_indices(kernel, supplied);
                        let invalid = apply_family(
                            kernel,
                            family_constants[target],
                            spec.params,
                            0,
                            &indices,
                        );
                        constructor_type(
                            kernel,
                            spec.params,
                            family_constants[family_index],
                            spec.index_counts[family_index],
                            &[(invalid, BinderInfo::Default)],
                            false,
                            binder,
                        )
                    }
                    Production::InvalidParameterOrIndex => {
                        let target = (spec.owner + 1) % spec.group_size;
                        let invalid = if spec.params.count() > 0 {
                            let mut app = family_constants[target];
                            for parameter in 0..spec.params.count() {
                                let value = if parameter == 0 {
                                    kernel.sort_zero()
                                } else {
                                    let depth = spec.params.count() - parameter - 1;
                                    kernel.bvar(u32::try_from(depth).unwrap())
                                };
                                app = kernel.app(app, value);
                            }
                            for index in constant_indices(kernel, spec.index_counts[target]) {
                                app = kernel.app(app, index);
                            }
                            app
                        } else {
                            let mut indices = constant_indices(kernel, spec.index_counts[target]);
                            if let Some(first) = indices.first_mut() {
                                *first = family_constants[target];
                            } else {
                                indices.push(family_constants[target]);
                            }
                            apply_family(kernel, family_constants[target], spec.params, 0, &indices)
                        };
                        constructor_type(
                            kernel,
                            spec.params,
                            family_constants[family_index],
                            spec.index_counts[family_index],
                            &[(invalid, BinderInfo::Default)],
                            false,
                            binder,
                        )
                    }
                    Production::ResultMismatch => {
                        let other = (family_index + 1) % spec.group_size;
                        let result = if other == family_index {
                            kernel.sort_zero()
                        } else {
                            let indices = constant_indices(kernel, spec.index_counts[other]);
                            apply_family(kernel, family_constants[other], spec.params, 0, &indices)
                        };
                        wrap_parameters(kernel, spec.params, binder, result)
                    }
                    _ => {
                        let mut fields = Vec::with_capacity(spec.total_fields);
                        let mut recursive_index = 0;
                        for position in 0..spec.total_fields {
                            if spec.recursive_positions.contains(&position) {
                                let target = recursive_targets[recursive_index];
                                target_counts[target] += 1;
                                let domain = recursive_field_type(
                                    kernel,
                                    family_constants[target],
                                    spec.params,
                                    spec.index_counts[target],
                                    position,
                                    spec.recursive_depths[recursive_index],
                                    spec.binder_infos[recursive_index],
                                    spec.field_dependent_indices
                                        && (spec.recursive_depths[recursive_index] > 0
                                            || spec.total_fields
                                                > spec.production.recursive_fields()),
                                    binder,
                                );
                                fields.push((domain, BinderInfo::Default));
                                recursive_index += 1;
                            } else {
                                let domain = sort_one(kernel);
                                let info = match (spec.ordinal + position) % 3 {
                                    0 => BinderInfo::Default,
                                    1 => BinderInfo::Implicit,
                                    _ => BinderInfo::StrictImplicit,
                                };
                                fields.push((domain, info));
                            }
                        }
                        constructor_type(
                            kernel,
                            spec.params,
                            family_constants[family_index],
                            spec.index_counts[family_index],
                            &fields,
                            spec.field_dependent_indices
                                && spec.total_fields > spec.production.recursive_fields(),
                            binder,
                        )
                    }
                }
            } else {
                base_constructor_type(
                    kernel,
                    spec.params,
                    family_constants[family_index],
                    spec.index_counts[family_index],
                    binder,
                )
            };
            constructors.push((constructor, ty));
            names.push(constructor);
            field_counts.push(pi_arity(kernel, ty) - spec.params.count());
            family_rule_targets.push(target_counts);
        }
        families.push(InductiveFamilySpec::new(
            family_names[family_index],
            family_type(
                kernel,
                spec.params,
                spec.index_counts[family_index],
                spec.family_sort,
                binder,
            ),
            constructors,
        ));
        constructor_names.push(names);
        constructor_field_counts.push(field_counts);
        rule_target_counts.push(family_rule_targets);
    }

    let minor_constructor_order = constructor_names.iter().flatten().copied().collect();

    let expected = ExpectedContract {
        family_names: family_names.clone(),
        constructor_names,
        constructor_field_counts,
        index_counts: spec.index_counts.clone(),
        is_recursive: spec.production.is_positive() && !recursive_targets.is_empty(),
        motive_family_order: family_names.clone(),
        minor_constructor_order,
        rule_target_counts,
    };
    (families, expected, family_names, recursor_names)
}

fn observe_contract(
    kernel: &mut Kernel,
    expected: &ExpectedContract,
    recursor_names: &[NameId],
    num_params: usize,
) -> ExpectedContract {
    let total_minors: usize = expected.constructor_names.iter().map(Vec::len).sum();
    let mut constructor_names = Vec::with_capacity(expected.family_names.len());
    let mut constructor_field_counts = Vec::with_capacity(expected.family_names.len());
    let mut index_counts = Vec::with_capacity(expected.family_names.len());
    let mut rule_target_counts = Vec::with_capacity(expected.family_names.len());
    let mut recursive_bits = BTreeSet::new();
    let mut observed_motive_order = None;
    let mut observed_minor_order = None;

    for (family_index, &family) in expected.family_names.iter().enumerate() {
        let Declaration::Inductive {
            num_params: actual_params,
            num_indices,
            is_recursive,
            ctor_names,
            ..
        } = kernel.environment().get(family).expect("admitted family")
        else {
            panic!("expected inductive declaration")
        };
        assert_eq!(usize::from(*actual_params), num_params);
        recursive_bits.insert(*is_recursive);
        index_counts.push(usize::from(*num_indices));
        constructor_names.push(ctor_names.clone());
        let mut family_field_counts = Vec::with_capacity(ctor_names.len());
        for (constructor_index, &constructor) in ctor_names.iter().enumerate() {
            let Declaration::Constructor {
                inductive,
                idx,
                num_fields,
                ..
            } = kernel
                .environment()
                .get(constructor)
                .expect("admitted constructor")
            else {
                panic!("expected constructor declaration")
            };
            assert_eq!(*inductive, family);
            assert_eq!(usize::from(*idx), constructor_index);
            family_field_counts.push(usize::from(*num_fields));
        }
        constructor_field_counts.push(family_field_counts);

        let declaration = kernel
            .environment()
            .get(recursor_names[family_index])
            .expect("generated recursor")
            .clone();
        let Declaration::Recursor {
            rec_rules,
            num_motives,
            num_minors,
            num_params: rec_params,
            num_indices: rec_indices,
            ..
        } = &declaration
        else {
            panic!("expected recursor declaration")
        };
        assert_eq!(usize::from(*num_motives), expected.family_names.len());
        assert_eq!(usize::from(*num_minors), total_minors);
        assert_eq!(usize::from(*rec_params), num_params);
        assert_eq!(
            usize::from(*rec_indices),
            expected.index_counts[family_index]
        );
        let inferred = kernel
            .infer(declaration.ty())
            .expect("recursor type infers");
        assert!(matches!(kernel.expr_node(inferred), ExprNode::Sort(_)));
        let all_constructors = expected
            .constructor_names
            .iter()
            .flatten()
            .copied()
            .collect::<Vec<_>>();
        let (motive_order, minor_order) = recursor_prefix_order(
            kernel,
            declaration.ty(),
            num_params,
            &expected.family_names,
            &all_constructors,
        );
        if let Some(order) = &observed_motive_order {
            assert_eq!(order, &motive_order, "all recursors share motive order");
        } else {
            observed_motive_order = Some(motive_order);
        }
        if let Some(order) = &observed_minor_order {
            assert_eq!(order, &minor_order, "all recursors share minor order");
        } else {
            observed_minor_order = Some(minor_order);
        }
        let rules = rec_rules
            .iter()
            .map(|rule| {
                recursor_names
                    .iter()
                    .map(|&target| count_constant(kernel, rule.value, target))
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        rule_target_counts.push(rules);
    }
    assert_eq!(
        recursive_bits.len(),
        1,
        "group recursive metadata is global"
    );
    ExpectedContract {
        family_names: expected.family_names.clone(),
        constructor_names,
        constructor_field_counts,
        index_counts,
        is_recursive: *recursive_bits.iter().next().unwrap(),
        motive_family_order: observed_motive_order.expect("nonempty group has motive order"),
        minor_constructor_order: observed_minor_order.expect("nonempty group has minor order"),
        rule_target_counts,
    }
}

fn assert_base_iota(
    kernel: &mut Kernel,
    spec: &CaseSpec,
    expected: &ExpectedContract,
    recursor_names: &[NameId],
) {
    let owner = spec.owner;
    let constructor = expected.constructor_names[owner][0];
    let recursor = recursor_names[owner];
    let rec_decl = kernel.environment().get(recursor).unwrap().clone();
    let levels = rec_decl
        .uparams()
        .iter()
        .map(|&parameter| kernel.level_param(parameter))
        .collect::<Vec<_>>();
    let params = (0..spec.params.count())
        .map(|position| kernel.fvar(10_000 + u64::try_from(position).unwrap()))
        .collect::<Vec<_>>();
    let motives = (0..spec.group_size)
        .map(|position| kernel.fvar(11_000 + u64::try_from(position).unwrap()))
        .collect::<Vec<_>>();
    let total_minors: usize = expected.constructor_names.iter().map(Vec::len).sum();
    let minors = (0..total_minors)
        .map(|position| kernel.fvar(12_000 + u64::try_from(position).unwrap()))
        .collect::<Vec<_>>();
    let owner_minor = expected.constructor_names[..owner]
        .iter()
        .map(Vec::len)
        .sum::<usize>();

    let mut major = kernel.const_(constructor, vec![]);
    for &parameter in &params {
        major = kernel.app(major, parameter);
    }
    let mut application = kernel.const_(recursor, levels);
    for argument in params.iter().chain(&motives).chain(&minors) {
        application = kernel.app(application, *argument);
    }
    for _ in 0..spec.index_counts[owner] {
        let index = kernel.sort_zero();
        application = kernel.app(application, index);
    }
    application = kernel.app(application, major);
    assert_eq!(
        kernel.whnf(application),
        minors[owner_minor],
        "{}: base-constructor iota selects its global minor",
        spec.id
    );
}

fn expected_error(spec: &CaseSpec, expected: &ExpectedContract) -> KernelError {
    let owner = expected.family_names[spec.owner];
    let constructor = expected.constructor_names[spec.owner][1];
    match spec.production {
        Production::NegativeDomain => KernelError::NonPositiveInductiveOccurrence {
            inductive: owner,
            ctor: constructor,
            field_index: 0,
        },
        Production::InvalidArity | Production::InvalidParameterOrIndex => {
            KernelError::InvalidInductiveOccurrence {
                inductive: owner,
                ctor: constructor,
                field_index: 0,
            }
        }
        Production::ResultMismatch => KernelError::ConstructorResultMismatch {
            expected: owner,
            ctor: constructor,
        },
        _ => panic!("positive production has no expected error"),
    }
}

fn increment(map: &mut BTreeMap<String, usize>, key: impl Into<String>) {
    *map.entry(key.into()).or_default() += 1;
}

fn descriptor_record(spec: &CaseSpec) -> String {
    format!(
        "{}|g={}|p={}|s={}|prod={}|d={}|owner={}|idx={:?}|ctors={:?}|fields={}|rpos={:?}|rtgt={:?}|rdepth={:?}|info={:?}|fdi={}",
        spec.id,
        spec.group_size,
        spec.params.label(),
        spec.family_sort.label(),
        spec.production.label(),
        spec.primary_depth,
        spec.owner,
        spec.index_counts,
        spec.constructor_counts,
        spec.total_fields,
        spec.recursive_positions,
        spec.recursive_targets,
        spec.recursive_depths,
        spec.binder_infos,
        spec.field_dependent_indices,
    )
}

fn fnv1a64(records: &[String]) -> u64 {
    let mut hash = 0xcbf2_9ce4_8422_2325_u64;
    for record in records {
        for byte in record.bytes().chain(b"\n".iter().copied()) {
            hash ^= u64::from(byte);
            hash = hash.wrapping_mul(0x0000_0100_0000_01b3);
        }
    }
    hash
}

fn render_counts(counts: &BTreeMap<String, usize>) -> String {
    counts
        .iter()
        .map(|(label, count)| format!("{label}:{count}"))
        .collect::<Vec<_>>()
        .join(",")
}

fn run_generated_grammar() -> String {
    let specs = generate_specs();
    assert_eq!(specs.len(), 720);
    assert_eq!(
        specs
            .iter()
            .map(|spec| &spec.id)
            .collect::<BTreeSet<_>>()
            .len(),
        specs.len(),
        "case identities must be unique"
    );

    let mut outcomes = BTreeMap::new();
    let mut groups = BTreeMap::new();
    let mut profiles = BTreeMap::new();
    let mut sorts = BTreeMap::new();
    let mut productions = BTreeMap::new();
    let mut depths = BTreeMap::new();
    let mut index_counts = BTreeMap::new();
    let mut constructor_counts = BTreeMap::new();
    let mut total_fields = BTreeMap::new();
    let mut recursive_fields = BTreeMap::new();
    let mut target_kinds = BTreeMap::new();
    let mut binder_infos = BTreeMap::new();
    let mut index_productions = BTreeMap::new();
    let mut mutations = BTreeMap::new();
    let mut mutation_coverage = BTreeSet::new();
    let mut records = Vec::with_capacity(specs.len());

    for spec in &specs {
        increment(&mut groups, spec.group_size.to_string());
        increment(&mut profiles, spec.params.label());
        increment(&mut sorts, spec.family_sort.label());
        increment(&mut productions, spec.production.label());
        increment(&mut depths, spec.primary_depth.to_string());
        for &count in &spec.index_counts {
            increment(&mut index_counts, count.to_string());
        }
        for &count in &spec.constructor_counts {
            increment(&mut constructor_counts, count.to_string());
        }
        increment(&mut total_fields, spec.total_fields.to_string());
        increment(
            &mut recursive_fields,
            spec.production.recursive_fields().to_string(),
        );
        for (&target, &depth) in spec.recursive_targets.iter().zip(&spec.recursive_depths) {
            let kind = match target.cmp(&spec.owner) {
                Ordering::Equal => "self",
                Ordering::Less => "earlier",
                Ordering::Greater => "later",
            };
            increment(&mut target_kinds, kind);
            increment(&mut depths, format!("recursive-{depth}"));
        }
        for &info in &spec.binder_infos {
            increment(&mut binder_infos, format!("{info:?}"));
        }
        if spec.production.is_positive() {
            for (&target, &depth) in spec.recursive_targets.iter().zip(&spec.recursive_depths) {
                let count = spec.index_counts[target];
                let dependent = spec.field_dependent_indices
                    && (depth > 0 || spec.total_fields > spec.production.recursive_fields());
                for index in 0..count {
                    let label = if dependent && index == 0 {
                        "recursive-field-dependent"
                    } else {
                        "recursive-constant"
                    };
                    increment(&mut index_productions, label);
                }
            }
            let result_dependent = spec.field_dependent_indices
                && spec.total_fields > spec.production.recursive_fields();
            for index in 0..spec.index_counts[spec.owner] {
                let label = if result_dependent && index == 0 {
                    "result-field-dependent"
                } else {
                    "result-constant"
                };
                increment(&mut index_productions, label);
            }
        }

        let mut kernel = Kernel::new();
        let before = environment_snapshot(&kernel);
        let (families, expected, _family_names, recursor_names) = build_case(&mut kernel, spec);
        let result = kernel.add_mutual_inductive(&[], spec.params.count(), &families);
        if spec.production.is_positive() {
            result.unwrap_or_else(|error| panic!("{} unexpectedly rejected: {error:?}", spec.id));
            increment(&mut outcomes, "admit");
            let observed =
                observe_contract(&mut kernel, &expected, &recursor_names, spec.params.count());
            assert_eq!(observed, expected, "{}: independent contract", spec.id);
            assert_base_iota(&mut kernel, spec, &expected, &recursor_names);

            if spec.group_size > 1 {
                let mut mutated = expected.clone();
                mutated.motive_family_order.swap(0, 1);
                if mutated.minor_constructor_order.len() > 1 {
                    mutated.minor_constructor_order.swap(0, 1);
                }
                assert_ne!(observed, mutated, "{}: group-order mutation", spec.id);
                mutation_coverage.insert(MutationClass::GroupOrder);
                increment(&mut mutations, MutationClass::GroupOrder.label());
            }
            if !spec.recursive_targets.is_empty() && spec.group_size > 1 {
                let mut mutated = expected.clone();
                let rule = &mut mutated.rule_target_counts[spec.owner][1];
                let source = spec.recursive_targets[0];
                let replacement = (source + 1) % spec.group_size;
                rule[source] -= 1;
                rule[replacement] += 1;
                assert_ne!(observed, mutated, "{}: target-family mutation", spec.id);
                mutation_coverage.insert(MutationClass::TargetFamily);
                increment(&mut mutations, MutationClass::TargetFamily.label());
            }
        } else {
            let error = result.expect_err("negative production must reject");
            assert_eq!(error, expected_error(spec, &expected), "{}: error", spec.id);
            assert_eq!(
                environment_snapshot(&kernel),
                before,
                "{}: rollback",
                spec.id
            );
            increment(&mut outcomes, "reject");
            mutation_coverage.insert(MutationClass::NegativeRollback);
            increment(&mut mutations, MutationClass::NegativeRollback.label());
        }
        records.push(descriptor_record(spec));
    }
    assert_eq!(
        mutation_coverage,
        BTreeSet::from([
            MutationClass::GroupOrder,
            MutationClass::TargetFamily,
            MutationClass::NegativeRollback,
        ])
    );

    format!(
        "schema=axeyum-lean-mutual-group-grammar-v1\n\
seed={GENERATOR_SEED:016x}\n\
cases={}\n\
outcomes={}\n\
group-sizes={}\n\
parameter-profiles={}\n\
sorts={}\n\
productions={}\n\
primary-and-recursive-depths={}\n\
per-family-index-counts={}\n\
per-family-constructor-counts={}\n\
selected-total-fields={}\n\
selected-recursive-fields={}\n\
recursive-targets={}\n\
recursive-binder-info={}\n\
selected-index-productions={}\n\
mutation-checks={}\n\
descriptor-fnv1a64={:016x}\n",
        specs.len(),
        render_counts(&outcomes),
        render_counts(&groups),
        render_counts(&profiles),
        render_counts(&sorts),
        render_counts(&productions),
        render_counts(&depths),
        render_counts(&index_counts),
        render_counts(&constructor_counts),
        render_counts(&total_fields),
        render_counts(&recursive_fields),
        render_counts(&target_kinds),
        render_counts(&binder_infos),
        render_counts(&index_productions),
        render_counts(&mutations),
        fnv1a64(&records),
    )
}

#[test]
fn generated_mutual_group_grammar_is_complete_and_byte_identical() {
    let first = run_generated_grammar();
    let second = run_generated_grammar();
    assert_eq!(
        first, second,
        "fixed-seed summary must repeat byte-for-byte"
    );
    assert_eq!(first, EXPECTED_GENERATED_SUMMARY);
}
