//! Independent deterministic public-path grammar for TL2.14 M3 nested
//! inductive elimination.
//!
//! Inputs and expected public contracts are derived from semantic case
//! records before [`Kernel::add_mutual_inductive`] runs. The observer reads
//! only the public environment and ordinary kernel operations.
#![allow(clippy::too_many_arguments, clippy::too_many_lines)]

use std::collections::{BTreeMap, BTreeSet};

use axeyum_lean_kernel::{
    BinderInfo, Declaration, ExprId, ExprNode, InductiveFamilySpec, Kernel, KernelError,
    LocalContext, LocalDecl, NameId,
};

const GENERATOR_SEED: u64 = 0x4158_4e45_5354_4d33;
const EXPECTED_GENERATED_SUMMARY: &str = "schema=axeyum-lean-nested-inductive-grammar-v1\n\
seed=41584e4553544d33\n\
cases=640\n\
outcomes=admit:320,reject:320\n\
errors=expansion-limit:1,incomplete-application:32,invalid-occurrence:96,loose-parameter:32,malformed-container:108,non-positive:32,public-collision:19\n\
productions=candidate-shape:64,capacity-or-publication:64,container-metadata:64,distinct-specializations:64,fixed-occurrence:64,higher-order-tail:64,nested-self:64,outer-sibling:64,parameter-shape:64,repeated-identical:64\n\
outer-group-sizes=1:216,2:216,3:208\n\
container-group-sizes=1:208,2:216,3:216\n\
outer-parameter-profiles=0p:160,1p:160,2p-dependent:160,2p-independent:160\n\
container-parameter-counts=1:200,2:240,3:200\n\
container-index-counts=0:216,1:216,2:208\n\
constructors-per-family=0:160,1:160,2:160,3:160\n\
fields-per-selected-constructor=0:78,1:82,2:84,3:82,4:78,5:76,no-constructor:160\n\
nested-applications=1:212,2:216,3:212\n\
nested-depths=1:320,2:320\n\
result-sorts=prop:320,type:320\n\
recursive-target-classes=container-auxiliary:208,outer-sibling:140,outer-sibling-fallback-self:84,self:208\n\
shape-variants=0:320,1:320\n\
index-variants=0:320,1:320\n\
source-owner-indices=0:397,1:181,2:62\n\
container-owner-indices=0:390,1:171,2:79\n\
active-parameter-slots=0:385,1:189,2:66\n\
binder-infos=Default:212,Implicit:213,StrictImplicit:215\n\
negative-subtypes=expansion-limit-sentinel:1,foreign-head:32,incomplete-parameter-prefix:32,late-public-rec-1-collision:19,loose-parameter:32,malformed-container-index-arity:40,negative-specialized-parameter:32,unregistered-constructor-metadata:16,unregistered-generic:16,unregistered-index-metadata:16,unregistered-recursion-metadata:16,wrong-fixed-source-parameter:24,wrong-universe-arity-one:23,wrong-universe-arity-two:21\n\
shallow-filler-positions=0:226,1:234,2:128,3:52\n\
published-auxiliary-counts=1:23,12:15,2:64,3:63,4:54,6:56,8:18,9:27\n\
public-recursor-dependency-edges=aux-to-aux:1044,aux-to-main:866,main-to-aux:644,main-to-main:168\n\
iota-checks=auxiliary:462,main:320\n\
mutation-checks=auxiliary-count-and-order:320,deduplicated-reuse:64,distinct-specialization:64,motive-and-minor-order:320,recursor-dependency-target:320,restored-rule-constructor-and-nfields:320,temporary-name-leakage:320,typed-rejection-rollback:320\n\
descriptor-fnv1a64=a20fe056c9443a37\n";

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
enum OuterParams {
    P0,
    P1,
    P2Independent,
    P2Dependent,
}

impl OuterParams {
    const ALL: [Self; 4] = [Self::P0, Self::P1, Self::P2Independent, Self::P2Dependent];

    const fn count(self) -> usize {
        match self {
            Self::P0 => 0,
            Self::P1 => 1,
            Self::P2Independent | Self::P2Dependent => 2,
        }
    }

    const fn label(self) -> &'static str {
        match self {
            Self::P0 => "0p",
            Self::P1 => "1p",
            Self::P2Independent => "2p-independent",
            Self::P2Dependent => "2p-dependent",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ResultSort {
    Type,
    Prop,
}

impl ResultSort {
    const ALL: [Self; 2] = [Self::Type, Self::Prop];

    const fn label(self) -> &'static str {
        match self {
            Self::Type => "type",
            Self::Prop => "prop",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Production {
    NestedSelf,
    RepeatedIdentical,
    DistinctSpecializations,
    HigherOrderTail,
    OuterSibling,
    CandidateShape,
    ParameterShape,
    FixedOccurrence,
    ContainerMetadata,
    CapacityOrPublication,
}

impl Production {
    const ALL: [Self; 10] = [
        Self::NestedSelf,
        Self::RepeatedIdentical,
        Self::DistinctSpecializations,
        Self::HigherOrderTail,
        Self::OuterSibling,
        Self::CandidateShape,
        Self::ParameterShape,
        Self::FixedOccurrence,
        Self::ContainerMetadata,
        Self::CapacityOrPublication,
    ];

    const fn label(self) -> &'static str {
        match self {
            Self::NestedSelf => "nested-self",
            Self::RepeatedIdentical => "repeated-identical",
            Self::DistinctSpecializations => "distinct-specializations",
            Self::HigherOrderTail => "higher-order-tail",
            Self::OuterSibling => "outer-sibling",
            Self::CandidateShape => "candidate-shape",
            Self::ParameterShape => "parameter-shape",
            Self::FixedOccurrence => "fixed-occurrence",
            Self::ContainerMetadata => "container-metadata",
            Self::CapacityOrPublication => "capacity-or-publication",
        }
    }

    const fn accepts(self) -> bool {
        matches!(
            self,
            Self::NestedSelf
                | Self::RepeatedIdentical
                | Self::DistinctSpecializations
                | Self::HigherOrderTail
                | Self::OuterSibling
        )
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum RecursiveTarget {
    SelfFamily,
    OuterSibling,
    ContainerAuxiliary,
}

impl RecursiveTarget {
    const ALL: [Self; 3] = [
        Self::SelfFamily,
        Self::OuterSibling,
        Self::ContainerAuxiliary,
    ];

    const fn label(self) -> &'static str {
        match self {
            Self::SelfFamily => "self",
            Self::OuterSibling => "outer-sibling",
            Self::ContainerAuxiliary => "container-auxiliary",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct CaseSpec {
    id: String,
    ordinal: usize,
    production: Production,
    outer_params: OuterParams,
    result_sort: ResultSort,
    depth: usize,
    shape_variant: usize,
    index_variant: usize,
    outer_group_size: usize,
    container_group_size: usize,
    container_params: usize,
    container_indices: usize,
    constructors_per_family: usize,
    fields_per_constructor: usize,
    nested_applications: usize,
    recursive_target: RecursiveTarget,
    source_owner: usize,
    owner: usize,
    active_parameter_slot: usize,
    binder_info: BinderInfo,
    negative_subtype: usize,
    shallow_filler_position: usize,
    limit_sentinel: bool,
}

#[derive(Clone, Debug)]
struct ContainerContract {
    family_names: Vec<NameId>,
    constructor_names: Vec<Vec<NameId>>,
    constructor_field_counts: Vec<Vec<usize>>,
    num_indices: usize,
}

#[derive(Clone, Debug)]
struct BuiltCase {
    source: Vec<InductiveFamilySpec>,
    source_names: Vec<NameId>,
    source_constructor_names: Vec<Vec<NameId>>,
    expected_auxiliaries: Vec<ExpectedAuxiliary>,
    expected_error: Option<ErrorClass>,
    filler_name: NameId,
}

#[derive(Clone, Debug)]
struct ExpectedAuxiliary {
    family_name: NameId,
    constructor_names: Vec<NameId>,
    constructor_field_counts: Vec<usize>,
    num_indices: usize,
    target_family: NameId,
    specialization: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum ErrorClass {
    IncompleteApplication,
    LooseParameter,
    NonPositive,
    InvalidOccurrence,
    MalformedContainer,
    ExpansionLimit,
    PublicCollision,
}

impl ErrorClass {
    const fn label(self) -> &'static str {
        match self {
            Self::IncompleteApplication => "incomplete-application",
            Self::LooseParameter => "loose-parameter",
            Self::NonPositive => "non-positive",
            Self::InvalidOccurrence => "invalid-occurrence",
            Self::MalformedContainer => "malformed-container",
            Self::ExpansionLimit => "expansion-limit",
            Self::PublicCollision => "public-collision",
        }
    }

    fn matches(self, error: &KernelError) -> bool {
        matches!(
            (self, error),
            (
                Self::IncompleteApplication,
                KernelError::NestedInductiveIncompleteApplication { .. }
            ) | (
                Self::LooseParameter,
                KernelError::NestedInductiveLooseParameter { .. }
            ) | (
                Self::NonPositive,
                KernelError::NonPositiveInductiveOccurrence { .. }
            ) | (
                Self::InvalidOccurrence,
                KernelError::InvalidInductiveOccurrence { .. }
            ) | (
                Self::MalformedContainer,
                KernelError::NestedInductiveMalformedContainer { .. }
            ) | (
                Self::ExpansionLimit,
                KernelError::NestedInductiveExpansionLimit { .. }
            ) | (Self::PublicCollision, KernelError::DeclarationExists { .. })
        )
    }
}

fn sort_one(kernel: &mut Kernel) -> ExprId {
    let zero = kernel.level_zero();
    let one = kernel.level_succ(zero);
    kernel.sort(one)
}

fn result_sort(kernel: &mut Kernel, sort: ResultSort) -> ExprId {
    match sort {
        ResultSort::Type => sort_one(kernel),
        ResultSort::Prop => kernel.sort_zero(),
    }
}

fn wrap_outer_params(
    kernel: &mut Kernel,
    params: OuterParams,
    binder: NameId,
    mut body: ExprId,
) -> ExprId {
    match params {
        OuterParams::P0 => body,
        OuterParams::P1 => {
            let domain = sort_one(kernel);
            kernel.pi(binder, domain, body, BinderInfo::Default)
        }
        OuterParams::P2Independent => {
            let domain = sort_one(kernel);
            body = kernel.pi(binder, domain, body, BinderInfo::Implicit);
            let domain = sort_one(kernel);
            kernel.pi(binder, domain, body, BinderInfo::Default)
        }
        OuterParams::P2Dependent => {
            let first = kernel.bvar(0);
            body = kernel.pi(binder, first, body, BinderInfo::StrictImplicit);
            let domain = sort_one(kernel);
            kernel.pi(binder, domain, body, BinderInfo::Default)
        }
    }
}

fn outer_param_values(
    kernel: &mut Kernel,
    params: OuterParams,
    inner_binders: usize,
) -> Vec<ExprId> {
    (0..params.count())
        .map(|parameter| {
            let depth = inner_binders + params.count() - parameter - 1;
            kernel.bvar(u32::try_from(depth).expect("generated depth fits u32"))
        })
        .collect()
}

fn apply_outer_family(
    kernel: &mut Kernel,
    family: ExprId,
    params: OuterParams,
    inner_binders: usize,
) -> ExprId {
    let mut result = family;
    for parameter in outer_param_values(kernel, params, inner_binders) {
        result = kernel.app(result, parameter);
    }
    result
}

fn wrap_independent_params(
    kernel: &mut Kernel,
    count: usize,
    domain: ExprId,
    binder: NameId,
    mut body: ExprId,
) -> ExprId {
    for index in (0..count).rev() {
        let info = match index % 3 {
            0 => BinderInfo::Default,
            1 => BinderInfo::Implicit,
            _ => BinderInfo::StrictImplicit,
        };
        body = kernel.pi(binder, domain, body, info);
    }
    body
}

fn independent_param_values(
    kernel: &mut Kernel,
    count: usize,
    inner_binders: usize,
) -> Vec<ExprId> {
    (0..count)
        .map(|parameter| {
            let depth = inner_binders + count - parameter - 1;
            kernel.bvar(u32::try_from(depth).expect("generated depth fits u32"))
        })
        .collect()
}

fn constant_indices(kernel: &mut Kernel, count: usize) -> Vec<ExprId> {
    (0..count).map(|_| kernel.sort_zero()).collect()
}

fn apply_container_family(
    kernel: &mut Kernel,
    family: ExprId,
    num_params: usize,
    inner_binders: usize,
    num_indices: usize,
) -> ExprId {
    let mut result = family;
    for parameter in independent_param_values(kernel, num_params, inner_binders) {
        result = kernel.app(result, parameter);
    }
    for index in constant_indices(kernel, num_indices) {
        result = kernel.app(result, index);
    }
    result
}

fn container_family_type(
    kernel: &mut Kernel,
    num_params: usize,
    num_indices: usize,
    sort: ResultSort,
    binder: NameId,
) -> ExprId {
    let mut ty = result_sort(kernel, sort);
    for index in (0..num_indices).rev() {
        let domain = sort_one(kernel);
        let info = if index % 2 == 0 {
            BinderInfo::Default
        } else {
            BinderInfo::Implicit
        };
        ty = kernel.pi(binder, domain, ty, info);
    }
    let parameter_domain = result_sort(kernel, sort);
    wrap_independent_params(kernel, num_params, parameter_domain, binder, ty)
}

fn container_constructor_type(
    kernel: &mut Kernel,
    owner: ExprId,
    recursive_target: ExprId,
    num_params: usize,
    num_indices: usize,
    fields: usize,
    binder: NameId,
    binder_info: BinderInfo,
) -> ExprId {
    let mut domains = Vec::with_capacity(fields);
    for position in 0..fields {
        let domain = if position == 0 {
            apply_container_family(kernel, recursive_target, num_params, position, num_indices)
        } else {
            independent_param_values(kernel, num_params, position)[0]
        };
        domains.push(domain);
    }
    let mut ty = apply_container_family(kernel, owner, num_params, fields, num_indices);
    for domain in domains.into_iter().rev() {
        ty = kernel.pi(binder, domain, ty, binder_info);
    }
    ty
}

fn declare_container_group(
    kernel: &mut Kernel,
    spec: &CaseSpec,
    prefix: &str,
) -> ContainerContract {
    let root = kernel.anon();
    let binder = kernel.name_str(root, "x");
    let family_names = (0..spec.container_group_size)
        .map(|index| kernel.name_str(root, format!("{prefix}F{index}")))
        .collect::<Vec<_>>();
    let family_constants = family_names
        .iter()
        .map(|&name| kernel.const_(name, vec![]))
        .collect::<Vec<_>>();
    let parameter_domain = result_sort(kernel, spec.result_sort);
    let mut families = Vec::with_capacity(family_names.len());
    let mut constructor_names = Vec::with_capacity(family_names.len());
    let mut constructor_field_counts = Vec::with_capacity(family_names.len());

    for family_index in 0..family_names.len() {
        let mut constructors = Vec::with_capacity(spec.constructors_per_family);
        let mut names = Vec::with_capacity(spec.constructors_per_family);
        let mut field_counts = Vec::with_capacity(spec.constructors_per_family);
        for constructor_index in 0..spec.constructors_per_family {
            let name = kernel.name_str(family_names[family_index], format!("c{constructor_index}"));
            let fields = if constructor_index == 0 {
                spec.fields_per_constructor
            } else {
                0
            };
            let recursive_target = match spec.recursive_target {
                RecursiveTarget::ContainerAuxiliary | RecursiveTarget::OuterSibling => {
                    (family_index + 1) % family_names.len()
                }
                RecursiveTarget::SelfFamily => family_index,
            };
            let body = container_constructor_type(
                kernel,
                family_constants[family_index],
                family_constants[recursive_target],
                spec.container_params,
                spec.container_indices,
                fields,
                binder,
                spec.binder_info,
            );
            let ty = wrap_independent_params(
                kernel,
                spec.container_params,
                parameter_domain,
                binder,
                body,
            );
            constructors.push((name, ty));
            names.push(name);
            field_counts.push(fields);
        }
        families.push(InductiveFamilySpec::new(
            family_names[family_index],
            container_family_type(
                kernel,
                spec.container_params,
                spec.container_indices,
                spec.result_sort,
                binder,
            ),
            constructors,
        ));
        constructor_names.push(names);
        constructor_field_counts.push(field_counts);
    }

    kernel
        .add_mutual_inductive(&[], spec.container_params, &families)
        .unwrap_or_else(|error| panic!("{}: container group rejected: {error:?}", spec.id));
    ContainerContract {
        family_names,
        constructor_names,
        constructor_field_counts,
        num_indices: spec.container_indices,
    }
}

fn declare_depth_two_wrapper(
    kernel: &mut Kernel,
    spec: &CaseSpec,
    container: &ContainerContract,
    prefix: &str,
) -> ContainerContract {
    let root = kernel.anon();
    let binder = kernel.name_str(root, "x");
    let family = kernel.name_str(root, format!("{prefix}Layer"));
    let constructor = kernel.name_str(family, "wrap");
    let family_const = kernel.const_(family, vec![]);
    let base_const = kernel.const_(
        container.family_names[spec.owner % container.family_names.len()],
        vec![],
    );
    let base = apply_container_family(
        kernel,
        base_const,
        spec.container_params,
        0,
        spec.container_indices,
    );
    let result = apply_container_family(kernel, family_const, spec.container_params, 1, 0);
    let body = kernel.pi(binder, base, result, BinderInfo::Default);
    let parameter_domain = result_sort(kernel, spec.result_sort);
    let constructor_type = wrap_independent_params(
        kernel,
        spec.container_params,
        parameter_domain,
        binder,
        body,
    );
    let family_type =
        container_family_type(kernel, spec.container_params, 0, spec.result_sort, binder);
    kernel
        .add_inductive(
            family,
            &[],
            spec.container_params,
            family_type,
            &[(constructor, constructor_type)],
        )
        .unwrap_or_else(|error| panic!("{}: depth-two wrapper rejected: {error:?}", spec.id));
    ContainerContract {
        family_names: vec![family],
        constructor_names: vec![vec![constructor]],
        constructor_field_counts: vec![vec![1]],
        num_indices: 0,
    }
}

fn declare_filler(kernel: &mut Kernel, spec: &CaseSpec, prefix: &str) -> NameId {
    let root = kernel.anon();
    let filler = kernel.name_str(root, format!("{prefix}Filler"));
    let ty = result_sort(kernel, spec.result_sort);
    kernel
        .add_declaration(Declaration::Axiom {
            name: filler,
            uparams: vec![],
            ty,
        })
        .expect("closed filler admits");
    filler
}

fn declare_one_field_container(kernel: &mut Kernel, spec: &CaseSpec, prefix: &str) -> NameId {
    let root = kernel.anon();
    let binder = kernel.name_str(root, "x");
    let family = kernel.name_str(root, format!("{prefix}OneField"));
    let constructor = kernel.name_str(family, "wrap");
    let domain = result_sort(kernel, spec.result_sort);
    let family_type = kernel.pi(binder, domain, domain, BinderInfo::Implicit);
    let family_const = kernel.const_(family, vec![]);
    let parameter = kernel.bvar(0);
    let result_parameter = kernel.bvar(1);
    let result = kernel.app(family_const, result_parameter);
    let body = kernel.pi(binder, parameter, result, BinderInfo::Default);
    let constructor_type = kernel.pi(binder, domain, body, BinderInfo::Implicit);
    kernel
        .add_inductive(
            family,
            &[],
            1,
            family_type,
            &[(constructor, constructor_type)],
        )
        .expect("one-field negative control container admits");
    family
}

fn specialize_target(
    kernel: &mut Kernel,
    target: ExprId,
    variant: usize,
    binder: NameId,
) -> ExprId {
    let mut result = target;
    for _ in 0..variant {
        result = kernel.lift_loose_bvars(result, 0, 1);
        let domain = kernel.sort_zero();
        result = kernel.pi(binder, domain, result, BinderInfo::Default);
    }
    result
}

fn build_nested_application(
    kernel: &mut Kernel,
    spec: &CaseSpec,
    selected_container: NameId,
    selected_indices: usize,
    target_family: ExprId,
    filler: NameId,
    preceding_fields: usize,
    specialization_variant: usize,
    higher_order_tail: bool,
    binder: NameId,
) -> ExprId {
    let higher_order_depth = usize::from(higher_order_tail);
    let target = apply_outer_family(
        kernel,
        target_family,
        spec.outer_params,
        preceding_fields + higher_order_depth,
    );
    let target = specialize_target(kernel, target, specialization_variant, binder);
    let mut nested = kernel.const_(selected_container, vec![]);
    for parameter in 0..spec.container_params {
        let argument = if parameter == spec.active_parameter_slot {
            target
        } else {
            kernel.const_(filler, vec![])
        };
        nested = kernel.app(nested, argument);
    }
    for index in constant_indices(kernel, selected_indices) {
        nested = kernel.app(nested, index);
    }
    if higher_order_tail {
        let domain = kernel.sort_zero();
        kernel.pi(binder, domain, nested, spec.binder_info)
    } else {
        nested
    }
}

fn outer_constructor_type(
    kernel: &mut Kernel,
    spec: &CaseSpec,
    owner: ExprId,
    fields: &[ExprId],
    binder: NameId,
) -> ExprId {
    let mut ty = apply_outer_family(kernel, owner, spec.outer_params, fields.len());
    for &field in fields.iter().rev() {
        ty = kernel.pi(binder, field, ty, spec.binder_info);
    }
    wrap_outer_params(kernel, spec.outer_params, binder, ty)
}

fn append_container_expectations(
    expected: &mut Vec<ExpectedAuxiliary>,
    container: &ContainerContract,
    target_family: NameId,
    specialization: usize,
) {
    for family in 0..container.family_names.len() {
        expected.push(ExpectedAuxiliary {
            family_name: container.family_names[family],
            constructor_names: container.constructor_names[family].clone(),
            constructor_field_counts: container.constructor_field_counts[family].clone(),
            num_indices: container.num_indices,
            target_family,
            specialization,
        });
    }
}

fn build_positive_case(
    kernel: &mut Kernel,
    spec: &CaseSpec,
    base: &ContainerContract,
    selected: &ContainerContract,
    filler: NameId,
    prefix: &str,
) -> BuiltCase {
    let root = kernel.anon();
    let binder = kernel.name_str(root, "x");
    let source_names = (0..spec.outer_group_size)
        .map(|family| kernel.name_str(root, format!("{prefix}Source{family}")))
        .collect::<Vec<_>>();
    let source_constants = source_names
        .iter()
        .map(|&name| kernel.const_(name, vec![]))
        .collect::<Vec<_>>();
    let source_constructor_names = source_names
        .iter()
        .map(|&family| vec![kernel.name_str(family, "node")])
        .collect::<Vec<_>>();
    let selected_name = selected.family_names[spec.owner % selected.family_names.len()];
    let selected_indices = selected.num_indices;
    let unique_applications = if spec.production == Production::RepeatedIdentical {
        1
    } else {
        spec.nested_applications
    };
    let mut application_contracts = Vec::with_capacity(unique_applications);
    let mut fields = Vec::with_capacity(spec.nested_applications + 2);
    for application in 0..spec.nested_applications {
        if application == spec.shallow_filler_position {
            fields.push(kernel.const_(filler, vec![]));
        }
        let target_index = if spec.production == Production::OuterSibling {
            (spec.source_owner + application + 1) % source_constants.len()
        } else {
            spec.source_owner
        };
        let specialization = if spec.production == Production::RepeatedIdentical {
            0
        } else {
            application
        };
        if application < unique_applications {
            application_contracts.push((source_names[target_index], specialization));
        }
        let nested = build_nested_application(
            kernel,
            spec,
            selected_name,
            selected_indices,
            source_constants[target_index],
            filler,
            fields.len(),
            specialization,
            spec.production == Production::HigherOrderTail,
            binder,
        );
        fields.push(nested);
    }
    if spec.shallow_filler_position == spec.nested_applications {
        fields.push(kernel.const_(filler, vec![]));
    }
    match spec.recursive_target {
        RecursiveTarget::SelfFamily => {
            let recursive = apply_outer_family(
                kernel,
                source_constants[spec.source_owner],
                spec.outer_params,
                fields.len(),
            );
            fields.push(recursive);
        }
        RecursiveTarget::OuterSibling if source_constants.len() > 1 => {
            let sibling = apply_outer_family(
                kernel,
                source_constants[(spec.source_owner + 1) % source_constants.len()],
                spec.outer_params,
                fields.len(),
            );
            fields.push(sibling);
        }
        RecursiveTarget::OuterSibling | RecursiveTarget::ContainerAuxiliary => {}
    }

    let mut source = Vec::with_capacity(source_names.len());
    for family in 0..source_names.len() {
        let constructor_fields = if family == spec.source_owner {
            fields.as_slice()
        } else {
            &[]
        };
        let constructor_type = outer_constructor_type(
            kernel,
            spec,
            source_constants[family],
            constructor_fields,
            binder,
        );
        let family_sort = result_sort(kernel, spec.result_sort);
        let family_type = wrap_outer_params(kernel, spec.outer_params, binder, family_sort);
        source.push(InductiveFamilySpec::new(
            source_names[family],
            family_type,
            vec![(source_constructor_names[family][0], constructor_type)],
        ));
    }

    let mut expected_auxiliaries = Vec::new();
    if spec.depth == 1 {
        for &(target_family, specialization) in &application_contracts {
            append_container_expectations(
                &mut expected_auxiliaries,
                base,
                target_family,
                specialization,
            );
        }
    } else {
        for &(target_family, specialization) in &application_contracts {
            append_container_expectations(
                &mut expected_auxiliaries,
                selected,
                target_family,
                specialization,
            );
        }
        for &(target_family, specialization) in &application_contracts {
            append_container_expectations(
                &mut expected_auxiliaries,
                base,
                target_family,
                specialization,
            );
        }
    }
    BuiltCase {
        source,
        source_names,
        source_constructor_names,
        expected_auxiliaries,
        expected_error: None,
        filler_name: filler,
    }
}

fn build_negative_case(
    kernel: &mut Kernel,
    spec: &CaseSpec,
    selected_container: &ContainerContract,
    filler: NameId,
    prefix: &str,
) -> BuiltCase {
    let root = kernel.anon();
    let binder = kernel.name_str(root, "x");
    let source_names = (0..spec.outer_group_size)
        .map(|family| kernel.name_str(root, format!("{prefix}BadSource{family}")))
        .collect::<Vec<_>>();
    let source_constants = source_names
        .iter()
        .map(|&name| kernel.const_(name, vec![]))
        .collect::<Vec<_>>();
    let source_constructor_names = source_names
        .iter()
        .enumerate()
        .map(|(family, &name)| {
            if family == spec.source_owner {
                vec![kernel.name_str(name, "node")]
            } else {
                Vec::new()
            }
        })
        .collect::<Vec<_>>();
    let constructor = source_constructor_names[spec.source_owner][0];
    let source_const = source_constants[spec.source_owner];
    let selected =
        selected_container.family_names[spec.owner % selected_container.family_names.len()];
    let source_at = |kernel: &mut Kernel, inner| {
        apply_outer_family(kernel, source_const, spec.outer_params, inner)
    };

    let (body, expected_error) = match spec.production {
        Production::CandidateShape if spec.negative_subtype == 0 => {
            let foreign = kernel.name_str(root, format!("{prefix}Foreign"));
            let domain = result_sort(kernel, spec.result_sort);
            let foreign_type = kernel.pi(binder, domain, domain, BinderInfo::Implicit);
            kernel
                .add_declaration(Declaration::Axiom {
                    name: foreign,
                    uparams: vec![],
                    ty: foreign_type,
                })
                .expect("foreign constructor admits");
            let foreign_const = kernel.const_(foreign, vec![]);
            let target = source_at(kernel, 0);
            let bad = kernel.app(foreign_const, target);
            let result = source_at(kernel, 1);
            (
                kernel.pi(binder, bad, result, BinderInfo::Default),
                ErrorClass::InvalidOccurrence,
            )
        }
        Production::CandidateShape => {
            let incomplete = kernel.name_str(root, format!("{prefix}Incomplete"));
            let domain = result_sort(kernel, spec.result_sort);
            let family_type = wrap_independent_params(kernel, 2, domain, binder, domain);
            kernel
                .add_inductive(incomplete, &[], 2, family_type, &[])
                .expect("empty two-parameter container admits");
            let head = kernel.const_(incomplete, vec![]);
            let target = source_at(kernel, 0);
            let bad = kernel.app(head, target);
            let result = source_at(kernel, 1);
            (
                kernel.pi(binder, bad, result, BinderInfo::Default),
                ErrorClass::IncompleteApplication,
            )
        }
        Production::ParameterShape if spec.negative_subtype == 0 => {
            let local_domain = result_sort(kernel, spec.result_sort);
            let target = source_at(kernel, 1);
            let escaping = kernel.bvar(1);
            let parameter = kernel.pi(binder, target, escaping, BinderInfo::Default);
            let mut bad = kernel.const_(selected, vec![]);
            for parameter_index in 0..spec.container_params {
                let argument = if parameter_index == spec.active_parameter_slot {
                    parameter
                } else {
                    kernel.const_(filler, vec![])
                };
                bad = kernel.app(bad, argument);
            }
            for index in constant_indices(kernel, selected_container.num_indices) {
                bad = kernel.app(bad, index);
            }
            let result = source_at(kernel, 2);
            let field = kernel.pi(binder, bad, result, BinderInfo::Default);
            (
                kernel.pi(binder, local_domain, field, BinderInfo::Default),
                ErrorClass::LooseParameter,
            )
        }
        Production::ParameterShape => {
            let selected = declare_one_field_container(kernel, spec, prefix);
            let target = source_at(kernel, 0);
            let filler_const = kernel.const_(filler, vec![]);
            let negative = kernel.pi(binder, target, filler_const, BinderInfo::Default);
            let mut bad = kernel.const_(selected, vec![]);
            bad = kernel.app(bad, negative);
            let result = source_at(kernel, 1);
            (
                kernel.pi(binder, bad, result, BinderInfo::Default),
                ErrorClass::NonPositive,
            )
        }
        Production::FixedOccurrence
            if spec.negative_subtype == 0 && spec.outer_params != OuterParams::P0 =>
        {
            let mut target = source_const;
            let outer_values = outer_param_values(kernel, spec.outer_params, 0);
            for (parameter_index, parameter) in outer_values.into_iter().enumerate() {
                let argument = if parameter_index == 0 {
                    kernel.sort_zero()
                } else {
                    parameter
                };
                target = kernel.app(target, argument);
            }
            let result = source_at(kernel, 1);
            (
                kernel.pi(binder, target, result, BinderInfo::Default),
                ErrorClass::InvalidOccurrence,
            )
        }
        Production::FixedOccurrence => {
            let mut bad = kernel.const_(selected, vec![]);
            let target = source_at(kernel, 0);
            for parameter_index in 0..spec.container_params {
                let argument = if parameter_index == spec.active_parameter_slot {
                    target
                } else {
                    kernel.const_(filler, vec![])
                };
                bad = kernel.app(bad, argument);
            }
            let supplied_indices = if selected_container.num_indices == 0 {
                1
            } else {
                selected_container.num_indices - 1
            };
            for index in constant_indices(kernel, supplied_indices) {
                bad = kernel.app(bad, index);
            }
            let result = source_at(kernel, 1);
            (
                kernel.pi(binder, bad, result, BinderInfo::Default),
                ErrorClass::InvalidOccurrence,
            )
        }
        Production::ContainerMetadata => {
            let fake = kernel.name_str(root, format!("{prefix}Unregistered"));
            let domain = result_sort(kernel, spec.result_sort);
            let fake_type = if spec.negative_subtype == 3 {
                let index_domain = sort_one(kernel);
                let result = kernel.pi(binder, index_domain, domain, BinderInfo::Default);
                kernel.pi(binder, domain, result, BinderInfo::Implicit)
            } else {
                kernel.pi(binder, domain, domain, BinderInfo::Implicit)
            };
            let bogus_ctor = kernel.name_str(fake, "bogus");
            kernel
                .add_declaration(Declaration::Inductive {
                    name: fake,
                    uparams: vec![],
                    ty: fake_type,
                    num_params: 1,
                    num_indices: u16::from(spec.negative_subtype == 3),
                    is_recursive: spec.negative_subtype == 2,
                    ctor_names: if spec.negative_subtype == 1 {
                        vec![bogus_ctor]
                    } else {
                        vec![]
                    },
                })
                .expect("generic declaration gate stages noncanonical metadata");
            let fake_const = kernel.const_(fake, vec![]);
            let target = source_at(kernel, 0);
            let bad = kernel.app(fake_const, target);
            let result = source_at(kernel, 1);
            (
                kernel.pi(binder, bad, result, BinderInfo::Default),
                ErrorClass::MalformedContainer,
            )
        }
        Production::CapacityOrPublication if spec.limit_sentinel => {
            let selected_const = kernel.const_(selected, vec![]);
            let mut ty = source_at(kernel, 0);
            for index in (0..=256_u64).rev() {
                let target = source_at(kernel, 0);
                let mut parameter = target;
                for _ in 0..=index {
                    parameter = kernel.pi(binder, target, parameter, BinderInfo::Default);
                }
                let mut nested = selected_const;
                for parameter_index in 0..spec.container_params {
                    let argument = if parameter_index == spec.active_parameter_slot {
                        parameter
                    } else {
                        kernel.const_(filler, vec![])
                    };
                    nested = kernel.app(nested, argument);
                }
                for index in constant_indices(kernel, spec.container_indices) {
                    nested = kernel.app(nested, index);
                }
                let field = kernel.name_num(constructor, index);
                ty = kernel.pi(field, nested, ty, BinderInfo::Default);
            }
            (ty, ErrorClass::ExpansionLimit)
        }
        Production::CapacityOrPublication if spec.negative_subtype == 0 => {
            let rec_1 = kernel.name_str(source_names[0], "rec_1");
            let ty = kernel.sort_zero();
            kernel
                .add_declaration(Declaration::Axiom {
                    name: rec_1,
                    uparams: vec![],
                    ty,
                })
                .expect("late public collision sentinel admits");
            let bad = build_nested_application(
                kernel,
                spec,
                selected,
                selected_container.num_indices,
                source_const,
                filler,
                0,
                0,
                false,
                binder,
            );
            let result = source_at(kernel, 1);
            (
                kernel.pi(binder, bad, result, BinderInfo::Default),
                ErrorClass::PublicCollision,
            )
        }
        Production::CapacityOrPublication => {
            let bogus_level = kernel.level_zero();
            let bogus_levels = if spec.negative_subtype == 2 {
                vec![bogus_level, bogus_level]
            } else {
                vec![bogus_level]
            };
            let mut bad = kernel.const_(selected, bogus_levels);
            let target = source_at(kernel, 0);
            for parameter_index in 0..spec.container_params {
                let argument = if parameter_index == spec.active_parameter_slot {
                    target
                } else {
                    kernel.const_(filler, vec![])
                };
                bad = kernel.app(bad, argument);
            }
            for index in constant_indices(kernel, selected_container.num_indices) {
                bad = kernel.app(bad, index);
            }
            let result = source_at(kernel, 1);
            (
                kernel.pi(binder, bad, result, BinderInfo::Default),
                ErrorClass::MalformedContainer,
            )
        }
        _ => unreachable!("negative builder called for positive production"),
    };
    // Every rejecting descriptor still realizes its registered source-group,
    // depth, nested-application, and recursive-target axes.  The scheduled
    // valid fields precede the single typed-reject witness, so the case is not
    // merely labelled with dimensions absent from the constructed term.
    let target_family = match spec.recursive_target {
        RecursiveTarget::SelfFamily | RecursiveTarget::ContainerAuxiliary => {
            source_constants[spec.source_owner]
        }
        RecursiveTarget::OuterSibling if source_constants.len() > 1 => {
            source_constants[(spec.source_owner + 1) % source_constants.len()]
        }
        RecursiveTarget::OuterSibling => source_constants[spec.source_owner],
    };
    let mut valid_fields = Vec::with_capacity(spec.nested_applications + 1);
    for application in 0..spec.nested_applications {
        if application == spec.shallow_filler_position {
            valid_fields.push(kernel.const_(filler, vec![]));
        }
        valid_fields.push(build_nested_application(
            kernel,
            spec,
            selected,
            selected_container.num_indices,
            target_family,
            filler,
            valid_fields.len(),
            application,
            false,
            binder,
        ));
    }
    if spec.shallow_filler_position == spec.nested_applications {
        valid_fields.push(kernel.const_(filler, vec![]));
    }
    let mut body = kernel.lift_loose_bvars(
        body,
        0,
        u32::try_from(valid_fields.len()).expect("generated field count fits u32"),
    );
    for field in valid_fields.into_iter().rev() {
        body = kernel.pi(binder, field, body, spec.binder_info);
    }
    let constructor_type = wrap_outer_params(kernel, spec.outer_params, binder, body);
    let mut source = Vec::with_capacity(source_names.len());
    for (family_index, &family_name) in source_names.iter().enumerate() {
        let family_sort = result_sort(kernel, spec.result_sort);
        let family_type = wrap_outer_params(kernel, spec.outer_params, binder, family_sort);
        let constructors = if family_index == spec.source_owner {
            vec![(constructor, constructor_type)]
        } else {
            Vec::new()
        };
        source.push(InductiveFamilySpec::new(
            family_name,
            family_type,
            constructors,
        ));
    }
    BuiltCase {
        source,
        source_names,
        source_constructor_names,
        expected_auxiliaries: Vec::new(),
        expected_error: Some(expected_error),
        filler_name: filler,
    }
}

fn generate_specs() -> Vec<CaseSpec> {
    let mut specs = Vec::with_capacity(640);
    let mut ordinal = 0;
    for (production_index, production) in Production::ALL.into_iter().enumerate() {
        for (outer_index, outer_params) in OuterParams::ALL.into_iter().enumerate() {
            for (sort_index, result_sort) in ResultSort::ALL.into_iter().enumerate() {
                for depth_index in 0..2 {
                    for shape_variant in 0..2 {
                        for index_variant in 0..2 {
                            let depth = depth_index + 1;
                            let outer_group_size =
                                1 + (production_index + outer_index + shape_variant) % 3;
                            let container_group_size = 1
                                + (production_index + sort_index + depth_index + index_variant) % 3;
                            let container_params =
                                1 + (outer_index + depth_index + shape_variant) % 3;
                            let container_indices =
                                (production_index + outer_index + index_variant) % 3;
                            let constructors_per_family = (production_index
                                + outer_index
                                + 2 * shape_variant
                                + index_variant)
                                % 4;
                            let fields_per_constructor = (production_index
                                + 2 * outer_index
                                + depth_index
                                + shape_variant
                                + index_variant)
                                % 6;
                            let nested_applications = 1
                                + (production_index + outer_index + shape_variant + index_variant)
                                    % 3;
                            let recursive_target = RecursiveTarget::ALL
                                [(production_index + sort_index + shape_variant) % 3];
                            let mut rng = Lcg(GENERATOR_SEED ^ u64::try_from(ordinal).unwrap());
                            let source_owner =
                                usize::try_from(rng.next_u64()).unwrap() % outer_group_size;
                            let owner =
                                usize::try_from(rng.next_u64()).unwrap() % container_group_size;
                            let active_parameter_slot =
                                usize::try_from(rng.next_u64()).unwrap() % container_params;
                            let binder_info = match rng.next_u64() % 3 {
                                0 => BinderInfo::Default,
                                1 => BinderInfo::Implicit,
                                _ => BinderInfo::StrictImplicit,
                            };
                            let negative_subtype = usize::try_from(rng.next_u64()).unwrap()
                                % match production {
                                    Production::CandidateShape
                                    | Production::ParameterShape
                                    | Production::FixedOccurrence => 2,
                                    Production::ContainerMetadata => 4,
                                    Production::CapacityOrPublication => 3,
                                    _ => 1,
                                };
                            let shallow_filler_position = usize::try_from(rng.next_u64()).unwrap()
                                % (nested_applications + 1);
                            let id = format!(
                                "{}-{}-{}-d{depth}-v{shape_variant}-x{index_variant}-o{ordinal:03}",
                                production.label(),
                                outer_params.label(),
                                result_sort.label(),
                            );
                            let limit_sentinel = production == Production::CapacityOrPublication
                                && outer_index == 0
                                && sort_index == 0
                                && depth_index == 0
                                && shape_variant == 0
                                && index_variant == 0;
                            specs.push(CaseSpec {
                                id,
                                ordinal,
                                production,
                                outer_params,
                                result_sort,
                                depth,
                                shape_variant,
                                index_variant,
                                outer_group_size,
                                container_group_size,
                                container_params,
                                container_indices,
                                constructors_per_family,
                                fields_per_constructor,
                                nested_applications,
                                recursive_target,
                                source_owner,
                                owner,
                                active_parameter_slot,
                                binder_info,
                                negative_subtype,
                                shallow_filler_position,
                                limit_sentinel,
                            });
                            ordinal += 1;
                        }
                    }
                }
            }
        }
    }
    specs
}

fn environment_snapshot(kernel: &Kernel) -> Vec<(NameId, Declaration)> {
    kernel
        .environment()
        .iter()
        .map(|(&name, declaration)| (name, declaration.clone()))
        .collect()
}

fn assert_no_temporary_names(kernel: &Kernel) {
    for (name, declaration) in kernel.environment().iter() {
        assert!(!kernel.display_name(*name).to_string().contains("_nested"));
        assert_no_temporary_names_in_expression(kernel, declaration.ty());
        if let Declaration::Recursor { rec_rules, .. } = declaration {
            for rule in rec_rules {
                assert_no_temporary_names_in_expression(kernel, rule.value);
            }
        }
    }
}

fn assert_no_temporary_names_in_expression(kernel: &Kernel, expression: ExprId) {
    match kernel.expr_node(expression).clone() {
        ExprNode::Const(name, _) => {
            assert!(!kernel.display_name(name).to_string().contains("_nested"));
        }
        ExprNode::Proj(type_name, _, structure) => {
            assert!(
                !kernel
                    .display_name(type_name)
                    .to_string()
                    .contains("_nested")
            );
            assert_no_temporary_names_in_expression(kernel, structure);
        }
        ExprNode::App(function, argument) => {
            assert_no_temporary_names_in_expression(kernel, function);
            assert_no_temporary_names_in_expression(kernel, argument);
        }
        ExprNode::Lam(_, ty, body, _) | ExprNode::Pi(_, ty, body, _) => {
            assert_no_temporary_names_in_expression(kernel, ty);
            assert_no_temporary_names_in_expression(kernel, body);
        }
        ExprNode::Let(_, ty, value, body) => {
            assert_no_temporary_names_in_expression(kernel, ty);
            assert_no_temporary_names_in_expression(kernel, value);
            assert_no_temporary_names_in_expression(kernel, body);
        }
        ExprNode::Sort(_) | ExprNode::BVar(_) | ExprNode::FVar(_) | ExprNode::Lit(_) => {}
    }
}

fn count_constant(kernel: &Kernel, expression: ExprId, target: NameId) -> usize {
    match kernel.expr_node(expression).clone() {
        ExprNode::Const(name, _) => usize::from(name == target),
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
        ExprNode::Sort(_) | ExprNode::BVar(_) | ExprNode::FVar(_) | ExprNode::Lit(_) => 0,
    }
}

fn unfold_apps(kernel: &Kernel, mut expression: ExprId) -> (ExprId, Vec<ExprId>) {
    let mut arguments = Vec::new();
    while let ExprNode::App(function, argument) = kernel.expr_node(expression).clone() {
        arguments.push(argument);
        expression = function;
    }
    arguments.reverse();
    (expression, arguments)
}

fn pi_binder_count(kernel: &Kernel, mut expression: ExprId) -> usize {
    let mut count = 0;
    while let ExprNode::Pi(_, _, body, _) = kernel.expr_node(expression) {
        count += 1;
        expression = *body;
    }
    count
}

fn motive_family_head(kernel: &Kernel, motive_type: ExprId) -> NameId {
    let major_domain = motive_major_domain(kernel, motive_type);
    let (head, _) = unfold_apps(kernel, major_domain);
    let ExprNode::Const(name, _) = kernel.expr_node(head).clone() else {
        panic!("motive major premise is headed by a public family constant");
    };
    name
}

fn motive_major_domain(kernel: &Kernel, mut motive_type: ExprId) -> ExprId {
    let mut major_domain = None;
    while let ExprNode::Pi(_, domain, body, _) = kernel.expr_node(motive_type).clone() {
        major_domain = Some(domain);
        motive_type = body;
    }
    major_domain.expect("motive type has a major premise")
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct SpecializedKey {
    family: NameId,
    target_family: NameId,
    specialization: usize,
    filler_slots: Vec<usize>,
    num_indices: usize,
}

fn specialized_key_from_motive(
    kernel: &Kernel,
    motive_type: ExprId,
    spec: &CaseSpec,
    filler_name: NameId,
) -> SpecializedKey {
    let major = motive_major_domain(kernel, motive_type);
    let (head, arguments) = unfold_apps(kernel, major);
    let ExprNode::Const(family, _) = kernel.expr_node(head).clone() else {
        panic!("specialized motive major has a constant family head");
    };
    assert!(arguments.len() >= spec.container_params);
    let mut filler_slots = Vec::new();
    let mut target = None;
    let mut specialization = 0;
    for (slot, &argument) in arguments[..spec.container_params].iter().enumerate() {
        if matches!(kernel.expr_node(argument), ExprNode::Const(name, _) if *name == filler_name) {
            filler_slots.push(slot);
            continue;
        }
        let mut cursor = argument;
        let mut depth = 0;
        while let ExprNode::Pi(_, _, body, _) = kernel.expr_node(cursor).clone() {
            depth += 1;
            cursor = body;
        }
        let (target_head, _) = unfold_apps(kernel, cursor);
        let ExprNode::Const(target_name, _) = kernel.expr_node(target_head).clone() else {
            panic!("specialized parameter has a source-family head");
        };
        assert!(target.replace(target_name).is_none());
        specialization = depth;
    }
    SpecializedKey {
        family,
        target_family: target.expect("one active specialized parameter"),
        specialization,
        filler_slots,
        num_indices: arguments.len() - spec.container_params,
    }
}

fn ordered_constructor_in(
    kernel: &Kernel,
    minor_type: ExprId,
    candidates: &BTreeSet<NameId>,
) -> NameId {
    let matches = candidates
        .iter()
        .copied()
        .filter(|&candidate| count_constant(kernel, minor_type, candidate) > 0)
        .collect::<Vec<_>>();
    assert_eq!(matches.len(), 1, "minor identifies exactly one constructor");
    matches[0]
}

fn recursor_prefix_order(
    kernel: &Kernel,
    recursor_type: ExprId,
    num_params: usize,
    num_motives: usize,
    num_minors: usize,
    constructor_candidates: &BTreeSet<NameId>,
) -> (Vec<NameId>, Vec<NameId>, Vec<ExprId>) {
    let mut cursor = recursor_type;
    for _ in 0..num_params {
        let ExprNode::Pi(_, _, body, _) = kernel.expr_node(cursor).clone() else {
            panic!("recursor parameter prefix is a Pi telescope");
        };
        cursor = body;
    }
    let mut motives = Vec::with_capacity(num_motives);
    let mut motive_domains = Vec::with_capacity(num_motives);
    for _ in 0..num_motives {
        let ExprNode::Pi(_, domain, body, _) = kernel.expr_node(cursor).clone() else {
            panic!("recursor motive prefix is a Pi telescope");
        };
        motives.push(motive_family_head(kernel, domain));
        motive_domains.push(domain);
        cursor = body;
    }
    let mut minors = Vec::with_capacity(num_minors);
    for _ in 0..num_minors {
        let ExprNode::Pi(_, domain, body, _) = kernel.expr_node(cursor).clone() else {
            panic!("recursor minor prefix is a Pi telescope");
        };
        minors.push(ordered_constructor_in(
            kernel,
            domain,
            constructor_candidates,
        ));
        cursor = body;
    }
    (motives, minors, motive_domains)
}

#[derive(Debug)]
struct PositiveObservation {
    auxiliary_count: usize,
    dependency_edges: BTreeMap<String, usize>,
    iota_checks: usize,
}

fn expected_dependency_edges(spec: &CaseSpec) -> BTreeMap<String, usize> {
    let mut expected = BTreeMap::new();
    expected.insert("main-to-aux".to_owned(), spec.nested_applications);
    let main_to_main = match spec.recursive_target {
        RecursiveTarget::SelfFamily => 1,
        RecursiveTarget::OuterSibling if spec.outer_group_size > 1 => 1,
        RecursiveTarget::OuterSibling | RecursiveTarget::ContainerAuxiliary => 0,
    };
    if main_to_main > 0 {
        expected.insert("main-to-main".to_owned(), main_to_main);
    }
    let specializations = if spec.production == Production::RepeatedIdentical {
        1
    } else {
        spec.nested_applications
    };
    let mut aux_to_aux = usize::from(spec.depth == 2) * specializations;
    let mut aux_to_main = 0;
    if spec.constructors_per_family > 0 && spec.fields_per_constructor > 0 {
        aux_to_aux += specializations * spec.container_group_size;
        if spec.active_parameter_slot == 0 {
            aux_to_main += specializations
                * spec.container_group_size
                * spec.fields_per_constructor.saturating_sub(1);
        }
    }
    if aux_to_aux > 0 {
        expected.insert("aux-to-aux".to_owned(), aux_to_aux);
    }
    if aux_to_main > 0 {
        expected.insert("aux-to-main".to_owned(), aux_to_main);
    }
    expected
}

fn add_expected_edge(
    edges: &mut BTreeMap<(NameId, NameId, NameId), usize>,
    source: NameId,
    rule: NameId,
    target: NameId,
    count: usize,
) {
    if count > 0 {
        *edges.entry((source, rule, target)).or_default() += count;
    }
}

fn expected_exact_dependency_edges(
    kernel: &mut Kernel,
    spec: &CaseSpec,
    built: &BuiltCase,
    source_recursors: &[NameId],
    auxiliary_recursors: &[NameId],
) -> BTreeMap<(NameId, NameId, NameId), usize> {
    let mut edges = BTreeMap::new();
    let source_rule = built.source_constructor_names[spec.source_owner][0];
    let specializations = if spec.production == Production::RepeatedIdentical {
        1
    } else {
        spec.nested_applications
    };
    for application in 0..spec.nested_applications {
        let specialization = if spec.production == Production::RepeatedIdentical {
            0
        } else {
            application
        };
        let auxiliary = if spec.depth == 1 {
            specialization * spec.container_group_size + spec.owner
        } else {
            specialization
        };
        add_expected_edge(
            &mut edges,
            source_recursors[spec.source_owner],
            source_rule,
            auxiliary_recursors[auxiliary],
            1,
        );
    }
    match spec.recursive_target {
        RecursiveTarget::SelfFamily => add_expected_edge(
            &mut edges,
            source_recursors[spec.source_owner],
            source_rule,
            source_recursors[spec.source_owner],
            1,
        ),
        RecursiveTarget::OuterSibling if source_recursors.len() > 1 => add_expected_edge(
            &mut edges,
            source_recursors[spec.source_owner],
            source_rule,
            source_recursors[(spec.source_owner + 1) % source_recursors.len()],
            1,
        ),
        RecursiveTarget::OuterSibling | RecursiveTarget::ContainerAuxiliary => {}
    }

    let base_start = usize::from(spec.depth == 2) * specializations;
    if spec.depth == 2 {
        for application in 0..specializations {
            let layer = application;
            let base = base_start + application * spec.container_group_size + spec.owner;
            add_expected_edge(
                &mut edges,
                auxiliary_recursors[layer],
                built.expected_auxiliaries[layer].constructor_names[0],
                auxiliary_recursors[base],
                1,
            );
        }
    }
    if spec.constructors_per_family > 0 && spec.fields_per_constructor > 0 {
        for application in 0..specializations {
            for family in 0..spec.container_group_size {
                let source = base_start + application * spec.container_group_size + family;
                let recursive_family = match spec.recursive_target {
                    RecursiveTarget::SelfFamily => family,
                    RecursiveTarget::OuterSibling | RecursiveTarget::ContainerAuxiliary => {
                        (family + 1) % spec.container_group_size
                    }
                };
                let target =
                    base_start + application * spec.container_group_size + recursive_family;
                let rule = built.expected_auxiliaries[source].constructor_names[0];
                add_expected_edge(
                    &mut edges,
                    auxiliary_recursors[source],
                    rule,
                    auxiliary_recursors[target],
                    1,
                );
                if spec.active_parameter_slot == 0 && spec.fields_per_constructor > 1 {
                    let target_family = built.expected_auxiliaries[source].target_family;
                    let target_main = built
                        .source_names
                        .iter()
                        .position(|&family| family == target_family)
                        .expect("specialized target is one source family");
                    add_expected_edge(
                        &mut edges,
                        auxiliary_recursors[source],
                        rule,
                        source_recursors[target_main],
                        spec.fields_per_constructor - 1,
                    );
                }
            }
        }
    }
    // Force the name arena use in this independent derivation to remain
    // explicit: all names above came from the public source/auxiliary vectors.
    let _ = kernel;
    edges
}

fn recursor_levels(
    kernel: &mut Kernel,
    declaration: &Declaration,
) -> Vec<axeyum_lean_kernel::LevelId> {
    declaration
        .uparams()
        .iter()
        .map(|&parameter| kernel.level_param(parameter))
        .collect()
}

fn fresh_typed_local(
    kernel: &mut Kernel,
    context: &mut LocalContext,
    name: NameId,
    ty: ExprId,
    info: BinderInfo,
) -> ExprId {
    kernel
        .infer_in(ty, context)
        .expect("generated local type infers in the open recursor context");
    let fvar = context.fresh_fvar();
    context.push(LocalDecl {
        fvar,
        name,
        ty,
        info,
    });
    kernel.fvar(fvar)
}

fn apply_open_telescope_locals(
    kernel: &mut Kernel,
    context: &mut LocalContext,
    mut application: ExprId,
    mut cursor: ExprId,
    count: usize,
) -> (ExprId, ExprId, Vec<ExprId>) {
    let mut values = Vec::with_capacity(count);
    for _ in 0..count {
        let ExprNode::Pi(name, domain, body, info) = kernel.expr_node(cursor).clone() else {
            panic!("public recursor exposes the registered Pi prefix");
        };
        let value = fresh_typed_local(kernel, context, name, domain, info);
        application = kernel.app(application, value);
        cursor = kernel.instantiate(body, &[value]);
        values.push(value);
    }
    (application, cursor, values)
}

fn synthesize_public_constructor_major(
    kernel: &mut Kernel,
    context: &mut LocalContext,
    expected_type: ExprId,
    excluded_families: &BTreeSet<NameId>,
    depth: usize,
    allow_fresh_fields: bool,
) -> Option<ExprId> {
    if let ExprNode::Pi(name, domain, body, info) = kernel.expr_node(expected_type).clone() {
        let fvar = context.fresh_fvar();
        context.push(LocalDecl {
            fvar,
            name,
            ty: domain,
            info,
        });
        let value = kernel.fvar(fvar);
        let instantiated = kernel.instantiate(body, &[value]);
        let synthesized = synthesize_public_constructor_major(
            kernel,
            context,
            instantiated,
            excluded_families,
            depth,
            allow_fresh_fields,
        );
        let synthesized = synthesized?;
        let body = kernel.abstract_fvars(synthesized, &[fvar]);
        let lambda = kernel.lam(name, domain, body, info);
        kernel
            .infer_in(lambda, context)
            .expect("synthesized higher-order constructor major is typed");
        return Some(lambda);
    }
    let (head, arguments) = unfold_apps(kernel, expected_type);
    let ExprNode::Const(family, _) = kernel.expr_node(head).clone() else {
        return None;
    };
    if excluded_families.contains(&family) {
        return None;
    }
    let Declaration::Inductive {
        num_params,
        ctor_names,
        ..
    } = kernel.environment().get(family)?.clone()
    else {
        return None;
    };
    let constructor = ctor_names.iter().copied().min_by_key(|&candidate| {
        match kernel.environment().get(candidate) {
            Some(Declaration::Constructor { num_fields, .. }) => *num_fields,
            _ => u16::MAX,
        }
    })?;
    let declaration = kernel.environment().get(constructor)?.clone();
    let Declaration::Constructor { uparams, ty, .. } = &declaration else {
        return None;
    };
    let levels = uparams
        .iter()
        .map(|&parameter| kernel.level_param(parameter))
        .collect::<Vec<_>>();
    let mut major = kernel.const_(constructor, levels);
    let mut cursor = *ty;
    for &parameter in arguments.iter().take(usize::from(num_params)) {
        let ExprNode::Pi(_, domain, body, _) = kernel.expr_node(cursor).clone() else {
            return None;
        };
        let inferred = kernel
            .infer_in(parameter, context)
            .expect("specialized constructor parameter is typed");
        assert!(kernel.def_eq_in(inferred, domain, context));
        major = kernel.app(major, parameter);
        cursor = kernel.instantiate(body, &[parameter]);
    }
    while let ExprNode::Pi(name, domain, body, info) = kernel.expr_node(cursor).clone() {
        let field = if depth > 0 {
            synthesize_public_constructor_major(
                kernel,
                context,
                domain,
                excluded_families,
                depth - 1,
                allow_fresh_fields,
            )
            .or_else(|| {
                allow_fresh_fields.then(|| fresh_typed_local(kernel, context, name, domain, info))
            })?
        } else if allow_fresh_fields {
            fresh_typed_local(kernel, context, name, domain, info)
        } else {
            return None;
        };
        major = kernel.app(major, field);
        cursor = kernel.instantiate(body, &[field]);
    }
    assert!(kernel.def_eq_in(cursor, expected_type, context));
    kernel
        .infer_in(major, context)
        .expect("synthesized public constructor major is typed");
    Some(major)
}

fn find_typed_recursor_call(
    kernel: &mut Kernel,
    context: &mut LocalContext,
    expression: ExprId,
    targets: &BTreeSet<NameId>,
) -> Option<(NameId, ExprId)> {
    let (head, _) = unfold_apps(kernel, expression);
    if let ExprNode::Const(name, _) = kernel.expr_node(head).clone()
        && targets.contains(&name)
    {
        return Some((name, expression));
    }
    match kernel.expr_node(expression).clone() {
        ExprNode::Proj(_, _, structure) => {
            find_typed_recursor_call(kernel, context, structure, targets)
        }
        ExprNode::App(function, argument) => {
            find_typed_recursor_call(kernel, context, function, targets)
                .or_else(|| find_typed_recursor_call(kernel, context, argument, targets))
        }
        ExprNode::Lam(name, ty, body, info) | ExprNode::Pi(name, ty, body, info) => {
            if let Some(found) = find_typed_recursor_call(kernel, context, ty, targets) {
                return Some(found);
            }
            let value = fresh_typed_local(kernel, context, name, ty, info);
            let body = kernel.instantiate(body, &[value]);
            if let Some(found) = find_typed_recursor_call(kernel, context, body, targets) {
                Some(found)
            } else {
                context.pop();
                None
            }
        }
        ExprNode::Let(_, ty, value, body) => find_typed_recursor_call(kernel, context, ty, targets)
            .or_else(|| find_typed_recursor_call(kernel, context, value, targets))
            .or_else(|| find_typed_recursor_call(kernel, context, body, targets)),
        ExprNode::Sort(_)
        | ExprNode::Const(..)
        | ExprNode::BVar(_)
        | ExprNode::FVar(_)
        | ExprNode::Lit(_) => None,
    }
}

fn assert_public_iota_chains(
    kernel: &mut Kernel,
    spec: &CaseSpec,
    built: &BuiltCase,
    source_recursors: &[NameId],
    auxiliary_recursors: &[NameId],
    expected_motives: usize,
    expected_minors: usize,
) -> usize {
    let mut context = LocalContext::new();
    let main_recursor = source_recursors[spec.source_owner];
    let main_declaration = kernel.environment().get(main_recursor).unwrap().clone();
    let main_levels = recursor_levels(kernel, &main_declaration);
    let mut main_application = kernel.const_(main_recursor, main_levels);
    let Declaration::Recursor {
        ty: main_type,
        num_params,
        num_indices,
        ..
    } = main_declaration
    else {
        unreachable!();
    };
    let prefix_count =
        usize::from(num_params) + expected_motives + expected_minors + usize::from(num_indices);
    let (application, main_cursor, prefix_values) = apply_open_telescope_locals(
        kernel,
        &mut context,
        main_application,
        main_type,
        prefix_count,
    );
    main_application = application;
    let parameter_values = &prefix_values[..usize::from(num_params)];
    let minor_start = usize::from(num_params) + expected_motives;
    let minor_values = &prefix_values[minor_start..minor_start + expected_minors];
    let ExprNode::Pi(_, expected_major_type, _, _) = kernel.expr_node(main_cursor).clone() else {
        panic!("main recursor ends in a major premise");
    };

    let source_constructor = built.source_constructor_names[spec.source_owner][0];
    let source_declaration = kernel
        .environment()
        .get(source_constructor)
        .unwrap()
        .clone();
    let Declaration::Constructor {
        uparams,
        ty: source_type,
        ..
    } = source_declaration
    else {
        unreachable!();
    };
    let source_levels = uparams
        .iter()
        .map(|&parameter| kernel.level_param(parameter))
        .collect::<Vec<_>>();
    let mut major = kernel.const_(source_constructor, source_levels);
    let mut source_cursor = source_type;
    for &parameter in parameter_values {
        let ExprNode::Pi(_, domain, body, _) = kernel.expr_node(source_cursor).clone() else {
            panic!("source constructor has the recursor parameter prefix");
        };
        let inferred = kernel.infer_in(parameter, &mut context).unwrap();
        assert!(kernel.def_eq_in(inferred, domain, &mut context));
        major = kernel.app(major, parameter);
        source_cursor = kernel.instantiate(body, &[parameter]);
    }
    let excluded_families = built.source_names.iter().copied().collect::<BTreeSet<_>>();
    let mut synthesized_nested_major = false;
    while let ExprNode::Pi(name, domain, body, info) = kernel.expr_node(source_cursor).clone() {
        let synthesized = synthesize_public_constructor_major(
            kernel,
            &mut context,
            domain,
            &excluded_families,
            spec.depth,
            true,
        );
        let field = if let Some(value) = synthesized {
            synthesized_nested_major = true;
            value
        } else {
            fresh_typed_local(kernel, &mut context, name, domain, info)
        };
        major = kernel.app(major, field);
        source_cursor = kernel.instantiate(body, &[field]);
    }
    assert!(kernel.def_eq_in(source_cursor, expected_major_type, &mut context));
    kernel
        .infer_in(major, &mut context)
        .expect("constructed source major is typed");
    main_application = kernel.app(main_application, major);
    kernel
        .infer_in(main_application, &mut context)
        .expect("complete public main iota redex is typed");
    let main_normal = kernel.whnf(main_application);
    let (main_head, _) = unfold_apps(kernel, main_normal);
    let source_minor = built.source_constructor_names[..spec.source_owner]
        .iter()
        .map(Vec::len)
        .sum::<usize>();
    assert_eq!(
        main_head, minor_values[source_minor],
        "{}: main iota minor",
        spec.id
    );

    if !synthesized_nested_major {
        assert!(
            built
                .expected_auxiliaries
                .iter()
                .all(|auxiliary| auxiliary.constructor_names.is_empty()),
            "{}: a constructible auxiliary major was unexpectedly absent",
            spec.id
        );
        return 1;
    }

    let auxiliary_set = auxiliary_recursors.iter().copied().collect::<BTreeSet<_>>();
    let first_expected_auxiliary = if spec.depth == 1 { spec.owner } else { 0 };
    let (first_name, mut call) =
        find_typed_recursor_call(kernel, &mut context, main_normal, &auxiliary_set)
            .expect("main iota result contains its concrete auxiliary recursive call");
    assert_eq!(
        first_name, auxiliary_recursors[first_expected_auxiliary],
        "{}: main-to-auxiliary chain target",
        spec.id
    );
    let mut reductions = 1;
    let mut visited = BTreeSet::new();
    while let Some((recursor, current_call)) =
        find_typed_recursor_call(kernel, &mut context, call, &auxiliary_set)
    {
        if !visited.insert((recursor, current_call)) {
            break;
        }
        kernel
            .infer_in(current_call, &mut context)
            .expect("produced auxiliary recursor call is typed");
        let normal = kernel.whnf(current_call);
        if normal == current_call {
            break;
        }
        let auxiliary_index = auxiliary_recursors
            .iter()
            .position(|&candidate| candidate == recursor)
            .unwrap();
        let (_, call_arguments) = unfold_apps(kernel, current_call);
        let major = kernel.whnf(*call_arguments.last().expect("recursor call has a major"));
        let (major_head, _) = unfold_apps(kernel, major);
        let ExprNode::Const(major_constructor, _) = kernel.expr_node(major_head).clone() else {
            panic!(
                "{}: concrete auxiliary major has a constructor head: {:?}",
                spec.id,
                kernel.expr_node(major_head)
            );
        };
        let constructor_index = built.expected_auxiliaries[auxiliary_index]
            .constructor_names
            .iter()
            .position(|&candidate| candidate == major_constructor)
            .expect("auxiliary major uses one registered constructor");
        let minor_index = built
            .source_constructor_names
            .iter()
            .map(Vec::len)
            .sum::<usize>()
            + built.expected_auxiliaries[..auxiliary_index]
                .iter()
                .map(|auxiliary| auxiliary.constructor_names.len())
                .sum::<usize>()
            + constructor_index;
        let (head, _) = unfold_apps(kernel, normal);
        assert_eq!(
            head, minor_values[minor_index],
            "{}: chained auxiliary iota minor {}",
            spec.id, auxiliary_index
        );
        reductions += 1;
        call = normal;
    }
    assert!(reductions >= 2, "{}: main-to-aux chain reduces", spec.id);
    reductions
}

fn observe_positive(
    kernel: &mut Kernel,
    spec: &CaseSpec,
    built: &BuiltCase,
) -> PositiveObservation {
    let expected_motives = built.source_names.len() + built.expected_auxiliaries.len();
    let expected_minors = built
        .source_constructor_names
        .iter()
        .map(Vec::len)
        .sum::<usize>()
        + built
            .expected_auxiliaries
            .iter()
            .map(|auxiliary| auxiliary.constructor_names.len())
            .sum::<usize>();

    for (family_index, &family) in built.source_names.iter().enumerate() {
        let Declaration::Inductive {
            uparams,
            ty,
            num_params,
            num_indices,
            ctor_names,
            ..
        } = kernel
            .environment()
            .get(family)
            .expect("source family published")
            .clone()
        else {
            panic!("{}: source family declaration kind", spec.id);
        };
        assert!(uparams.is_empty(), "{}", spec.id);
        assert!(
            kernel.def_eq(ty, built.source[family_index].ty),
            "{}",
            spec.id
        );
        assert_eq!(
            usize::from(num_params),
            spec.outer_params.count(),
            "{}",
            spec.id
        );
        assert_eq!(num_indices, 0, "{}", spec.id);
        assert_eq!(
            &ctor_names, &built.source_constructor_names[family_index],
            "{}",
            spec.id
        );
        for (constructor_index, (&(constructor, source_ty), &expected_name)) in built.source
            [family_index]
            .constructors
            .iter()
            .zip(&built.source_constructor_names[family_index])
            .enumerate()
        {
            assert_eq!(constructor, expected_name);
            let declaration = kernel
                .environment()
                .get(constructor)
                .expect("source constructor published")
                .clone();
            let Declaration::Constructor {
                uparams,
                inductive,
                idx,
                num_fields,
                ..
            } = &declaration
            else {
                panic!("{}: source constructor declaration kind", spec.id);
            };
            assert!(uparams.is_empty(), "{}", spec.id);
            assert_eq!(*inductive, family, "{}", spec.id);
            assert_eq!(usize::from(*idx), constructor_index, "{}", spec.id);
            assert_eq!(
                usize::from(*num_fields),
                pi_binder_count(kernel, source_ty) - spec.outer_params.count(),
                "{}",
                spec.id
            );
            assert!(
                kernel.def_eq(declaration.ty(), source_ty),
                "{}: restored source type",
                spec.id
            );
        }
        let recursor = kernel.name_str(family, "rec");
        let Declaration::Recursor {
            num_motives,
            num_minors,
            num_params,
            ..
        } = kernel
            .environment()
            .get(recursor)
            .expect("main recursor published")
        else {
            panic!("{}: main recursor declaration kind", spec.id);
        };
        assert_eq!(usize::from(*num_motives), expected_motives, "{}", spec.id);
        assert_eq!(usize::from(*num_minors), expected_minors, "{}", spec.id);
        assert_eq!(
            usize::from(*num_params),
            spec.outer_params.count(),
            "{}",
            spec.id
        );
    }

    let source_recursors = built
        .source_names
        .iter()
        .map(|&family| kernel.name_str(family, "rec"))
        .collect::<Vec<_>>();
    let main_rec = source_recursors[0];
    let mut auxiliary_recursors = Vec::with_capacity(built.expected_auxiliaries.len());
    for (index, expected) in built.expected_auxiliaries.iter().enumerate() {
        let Declaration::Inductive {
            uparams,
            num_params: original_num_params,
            num_indices: original_num_indices,
            ctor_names: original_ctor_names,
            ..
        } = kernel
            .environment()
            .get(expected.family_name)
            .expect("original container family remains public")
        else {
            panic!("{}: original container declaration kind", spec.id);
        };
        assert!(uparams.is_empty(), "{}", spec.id);
        assert_eq!(usize::from(*original_num_params), spec.container_params);
        assert_eq!(usize::from(*original_num_indices), expected.num_indices);
        assert_eq!(original_ctor_names, &expected.constructor_names);
        for (constructor_index, (&constructor, &expected_fields)) in expected
            .constructor_names
            .iter()
            .zip(&expected.constructor_field_counts)
            .enumerate()
        {
            let Declaration::Constructor {
                uparams,
                inductive,
                idx,
                num_fields,
                ..
            } = kernel.environment().get(constructor).unwrap()
            else {
                panic!("{}: original constructor declaration kind", spec.id);
            };
            assert!(uparams.is_empty(), "{}", spec.id);
            assert_eq!(*inductive, expected.family_name, "{}", spec.id);
            assert_eq!(usize::from(*idx), constructor_index, "{}", spec.id);
            assert_eq!(usize::from(*num_fields), expected_fields, "{}", spec.id);
        }
        let public_name = match kernel.name_node(main_rec).clone() {
            axeyum_lean_kernel::NameNode::Str(parent, component) => {
                kernel.name_str(parent, format!("{component}_{}", index + 1))
            }
            _ => kernel.name_num(main_rec, u64::try_from(index + 1).unwrap()),
        };
        auxiliary_recursors.push(public_name);
        let Declaration::Recursor {
            rec_rules,
            num_motives,
            num_minors,
            num_params,
            num_indices,
            ..
        } = kernel
            .environment()
            .get(public_name)
            .unwrap_or_else(|| panic!("{}: missing auxiliary recursor {}", spec.id, index + 1))
        else {
            panic!("{}: auxiliary declaration kind", spec.id);
        };
        assert_eq!(usize::from(*num_motives), expected_motives, "{}", spec.id);
        assert_eq!(usize::from(*num_minors), expected_minors, "{}", spec.id);
        assert_eq!(
            usize::from(*num_params),
            spec.outer_params.count(),
            "{}",
            spec.id
        );
        assert_eq!(
            usize::from(*num_indices),
            expected.num_indices,
            "{}",
            spec.id
        );
        assert_eq!(
            rec_rules.len(),
            expected.constructor_names.len(),
            "{}",
            spec.id
        );
        for ((rule, &constructor), &fields) in rec_rules
            .iter()
            .zip(&expected.constructor_names)
            .zip(&expected.constructor_field_counts)
        {
            assert_eq!(rule.ctor_name, constructor, "{}", spec.id);
            assert_eq!(usize::from(rule.num_fields), fields, "{}", spec.id);
        }
    }
    let next = match kernel.name_node(main_rec).clone() {
        axeyum_lean_kernel::NameNode::Str(parent, component) => kernel.name_str(
            parent,
            format!("{component}_{}", built.expected_auxiliaries.len() + 1),
        ),
        _ => kernel.name_num(
            main_rec,
            u64::try_from(built.expected_auxiliaries.len() + 1).unwrap(),
        ),
    };
    assert!(
        !kernel.environment().contains(next),
        "{}: extra auxiliary",
        spec.id
    );

    let expected_motive_order = built
        .source_names
        .iter()
        .copied()
        .chain(
            built
                .expected_auxiliaries
                .iter()
                .map(|auxiliary| auxiliary.family_name),
        )
        .collect::<Vec<_>>();
    let expected_minor_order = built
        .source_constructor_names
        .iter()
        .flatten()
        .copied()
        .chain(
            built
                .expected_auxiliaries
                .iter()
                .flat_map(|auxiliary| auxiliary.constructor_names.iter().copied()),
        )
        .collect::<Vec<_>>();
    let constructor_candidates = expected_minor_order
        .iter()
        .copied()
        .collect::<BTreeSet<_>>();
    let all_recursors = source_recursors
        .iter()
        .copied()
        .chain(auxiliary_recursors.iter().copied())
        .collect::<Vec<_>>();
    for &recursor in &all_recursors {
        let declaration = kernel.environment().get(recursor).unwrap();
        let (motives, minors, motive_domains) = recursor_prefix_order(
            kernel,
            declaration.ty(),
            spec.outer_params.count(),
            expected_motives,
            expected_minors,
            &constructor_candidates,
        );
        assert_eq!(motives, expected_motive_order, "{}: motive order", spec.id);
        assert_eq!(minors, expected_minor_order, "{}: minor order", spec.id);
        for (auxiliary_index, expected) in built.expected_auxiliaries.iter().enumerate() {
            let observed = specialized_key_from_motive(
                kernel,
                motive_domains[built.source_names.len() + auxiliary_index],
                spec,
                built.filler_name,
            );
            let expected_key = SpecializedKey {
                family: expected.family_name,
                target_family: expected.target_family,
                specialization: expected.specialization,
                filler_slots: (0..spec.container_params)
                    .filter(|slot| *slot != spec.active_parameter_slot)
                    .collect(),
                num_indices: expected.num_indices,
            };
            assert_eq!(
                observed, expected_key,
                "{}: specialized auxiliary key {}",
                spec.id, auxiliary_index
            );
        }
    }

    let source_recursor_set = source_recursors.iter().copied().collect::<BTreeSet<_>>();
    let auxiliary_recursor_set = auxiliary_recursors.iter().copied().collect::<BTreeSet<_>>();
    let mut dependency_edges = BTreeMap::new();
    let mut exact_dependency_edges = BTreeMap::new();
    for &recursor in &all_recursors {
        let source_kind = if source_recursor_set.contains(&recursor) {
            "main"
        } else {
            "aux"
        };
        let Declaration::Recursor { rec_rules, .. } = kernel.environment().get(recursor).unwrap()
        else {
            unreachable!();
        };
        for rule in rec_rules {
            for &target in &source_recursors {
                let count = count_constant(kernel, rule.value, target);
                if count > 0 {
                    exact_dependency_edges.insert((recursor, rule.ctor_name, target), count);
                    *dependency_edges
                        .entry(format!("{source_kind}-to-main"))
                        .or_default() += count;
                }
            }
            for &target in &auxiliary_recursors {
                let count = count_constant(kernel, rule.value, target);
                if count > 0 {
                    exact_dependency_edges.insert((recursor, rule.ctor_name, target), count);
                    *dependency_edges
                        .entry(format!("{source_kind}-to-aux"))
                        .or_default() += count;
                }
            }
        }
    }
    assert!(
        source_recursor_set.is_disjoint(&auxiliary_recursor_set),
        "{}: public recursor classes are disjoint",
        spec.id
    );
    assert_eq!(
        dependency_edges,
        expected_dependency_edges(spec),
        "{}: independent dependency edges",
        spec.id
    );
    assert_eq!(
        exact_dependency_edges,
        expected_exact_dependency_edges(
            kernel,
            spec,
            built,
            &source_recursors,
            &auxiliary_recursors,
        ),
        "{}: exact per-recursor/rule/target dependency edges",
        spec.id
    );
    let iota_checks = assert_public_iota_chains(
        kernel,
        spec,
        built,
        &source_recursors,
        &auxiliary_recursors,
        expected_motives,
        expected_minors,
    );

    let declarations = kernel
        .environment()
        .iter()
        .map(|(_, declaration)| declaration.clone())
        .collect::<Vec<_>>();
    for declaration in declarations {
        let inferred = kernel
            .infer(declaration.ty())
            .unwrap_or_else(|error| panic!("{}: public type failed inference: {error:?}", spec.id));
        assert!(
            matches!(kernel.expr_node(inferred), ExprNode::Sort(_)),
            "{}",
            spec.id
        );
        if let Declaration::Recursor { rec_rules, .. } = declaration {
            for rule in rec_rules {
                kernel.infer(rule.value).unwrap_or_else(|error| {
                    panic!("{}: public rule failed inference: {error:?}", spec.id)
                });
            }
        }
    }
    assert_no_temporary_names(kernel);
    PositiveObservation {
        auxiliary_count: built.expected_auxiliaries.len(),
        dependency_edges,
        iota_checks,
    }
}

fn descriptor_record(spec: &CaseSpec) -> String {
    format!(
        "{}|{}|{}|{}|{}|{}|{}|{}|{}|{}|{}|{}|{}|{}|{}|{}|{}|{}|{}|{:?}|{}|{}|{}|{}",
        spec.id,
        spec.production.label(),
        spec.outer_params.label(),
        spec.result_sort.label(),
        spec.depth,
        spec.shape_variant,
        spec.index_variant,
        spec.outer_group_size,
        spec.container_group_size,
        spec.container_params,
        spec.container_indices,
        spec.constructors_per_family,
        spec.fields_per_constructor,
        spec.nested_applications,
        spec.recursive_target.label(),
        realized_recursive_target_label(spec),
        spec.source_owner,
        spec.owner,
        spec.active_parameter_slot,
        spec.binder_info,
        spec.negative_subtype,
        realized_negative_subtype_label(spec),
        spec.shallow_filler_position,
        spec.limit_sentinel,
    )
}

fn realized_negative_subtype_label(spec: &CaseSpec) -> &'static str {
    match spec.production {
        Production::CandidateShape if spec.negative_subtype == 0 => "foreign-head",
        Production::CandidateShape => "incomplete-parameter-prefix",
        Production::ParameterShape if spec.negative_subtype == 0 => "loose-parameter",
        Production::ParameterShape => "negative-specialized-parameter",
        Production::FixedOccurrence
            if spec.negative_subtype == 0 && spec.outer_params != OuterParams::P0 =>
        {
            "wrong-fixed-source-parameter"
        }
        Production::FixedOccurrence => "malformed-container-index-arity",
        Production::ContainerMetadata if spec.negative_subtype == 0 => "unregistered-generic",
        Production::ContainerMetadata if spec.negative_subtype == 1 => {
            "unregistered-constructor-metadata"
        }
        Production::ContainerMetadata if spec.negative_subtype == 2 => {
            "unregistered-recursion-metadata"
        }
        Production::ContainerMetadata => "unregistered-index-metadata",
        Production::CapacityOrPublication if spec.limit_sentinel => "expansion-limit-sentinel",
        Production::CapacityOrPublication if spec.negative_subtype == 0 => {
            "late-public-rec-1-collision"
        }
        Production::CapacityOrPublication if spec.negative_subtype == 1 => {
            "wrong-universe-arity-one"
        }
        Production::CapacityOrPublication => "wrong-universe-arity-two",
        _ => "accepted",
    }
}

fn realized_recursive_target_label(spec: &CaseSpec) -> &'static str {
    match spec.recursive_target {
        RecursiveTarget::SelfFamily => "self",
        RecursiveTarget::ContainerAuxiliary => "container-auxiliary",
        RecursiveTarget::OuterSibling if spec.outer_group_size > 1 => "outer-sibling",
        RecursiveTarget::OuterSibling => "outer-sibling-fallback-self",
    }
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

fn increment(counts: &mut BTreeMap<String, usize>, label: impl Into<String>) {
    *counts.entry(label.into()).or_default() += 1;
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
    assert_eq!(specs.len(), 640);
    assert_eq!(
        specs
            .iter()
            .map(|spec| &spec.id)
            .collect::<BTreeSet<_>>()
            .len(),
        640,
        "case identities must be unique"
    );
    let descriptors = specs.iter().map(descriptor_record).collect::<Vec<_>>();
    assert_eq!(descriptors.iter().collect::<BTreeSet<_>>().len(), 640);

    let mut outcomes = BTreeMap::new();
    let mut errors = BTreeMap::new();
    let mut productions = BTreeMap::new();
    let mut outer_groups = BTreeMap::new();
    let mut container_groups = BTreeMap::new();
    let mut outer_params = BTreeMap::new();
    let mut container_params = BTreeMap::new();
    let mut container_indices = BTreeMap::new();
    let mut constructors = BTreeMap::new();
    let mut fields = BTreeMap::new();
    let mut nested_apps = BTreeMap::new();
    let mut depths = BTreeMap::new();
    let mut sorts = BTreeMap::new();
    let mut targets = BTreeMap::new();
    let mut shape_variants = BTreeMap::new();
    let mut index_variants = BTreeMap::new();
    let mut source_owners = BTreeMap::new();
    let mut container_owners = BTreeMap::new();
    let mut active_parameter_slots = BTreeMap::new();
    let mut binder_infos = BTreeMap::new();
    let mut negative_subtypes = BTreeMap::new();
    let mut filler_positions = BTreeMap::new();
    let mut auxiliary_counts = BTreeMap::new();
    let mut dependency_edges = BTreeMap::new();
    let mut iota_checks = BTreeMap::new();
    let mut mutation_checks = BTreeMap::new();

    for spec in &specs {
        increment(&mut productions, spec.production.label());
        increment(&mut outer_groups, spec.outer_group_size.to_string());
        increment(&mut container_groups, spec.container_group_size.to_string());
        increment(&mut outer_params, spec.outer_params.label());
        increment(&mut container_params, spec.container_params.to_string());
        increment(&mut container_indices, spec.container_indices.to_string());
        increment(&mut constructors, spec.constructors_per_family.to_string());
        increment(
            &mut fields,
            if spec.constructors_per_family == 0 {
                "no-constructor".to_owned()
            } else {
                spec.fields_per_constructor.to_string()
            },
        );
        increment(&mut nested_apps, spec.nested_applications.to_string());
        increment(&mut depths, spec.depth.to_string());
        increment(&mut sorts, spec.result_sort.label());
        increment(&mut targets, realized_recursive_target_label(spec));
        increment(&mut shape_variants, spec.shape_variant.to_string());
        increment(&mut index_variants, spec.index_variant.to_string());
        increment(&mut source_owners, spec.source_owner.to_string());
        increment(&mut container_owners, spec.owner.to_string());
        increment(
            &mut active_parameter_slots,
            spec.active_parameter_slot.to_string(),
        );
        increment(&mut binder_infos, format!("{:?}", spec.binder_info));
        if !spec.production.accepts() {
            increment(
                &mut negative_subtypes,
                realized_negative_subtype_label(spec),
            );
        }
        increment(
            &mut filler_positions,
            spec.shallow_filler_position.to_string(),
        );

        let mut kernel = Kernel::new();
        let prefix = format!("M3N{}", spec.ordinal);
        let base = declare_container_group(&mut kernel, spec, &prefix);
        let selected = if spec.depth == 2 {
            declare_depth_two_wrapper(&mut kernel, spec, &base, &prefix)
        } else {
            base.clone()
        };
        let filler = declare_filler(&mut kernel, spec, &prefix);
        let built = if spec.production.accepts() {
            build_positive_case(&mut kernel, spec, &base, &selected, filler, &prefix)
        } else {
            build_negative_case(&mut kernel, spec, &selected, filler, &prefix)
        };
        let before = environment_snapshot(&kernel);
        let result = kernel.add_mutual_inductive(&[], spec.outer_params.count(), &built.source);
        if spec.production.accepts() {
            result.unwrap_or_else(|error| panic!("{} unexpectedly rejected: {error:?}", spec.id));
            let observation = observe_positive(&mut kernel, spec, &built);
            increment(&mut outcomes, "admit");
            increment(
                &mut auxiliary_counts,
                observation.auxiliary_count.to_string(),
            );
            for (label, count) in observation.dependency_edges {
                *dependency_edges.entry(label).or_default() += count;
            }
            increment(&mut iota_checks, "main");
            *iota_checks.entry("auxiliary".to_owned()).or_default() += observation.iota_checks - 1;
            for mutation in [
                "auxiliary-count-and-order",
                "motive-and-minor-order",
                "recursor-dependency-target",
                "restored-rule-constructor-and-nfields",
                "temporary-name-leakage",
            ] {
                increment(&mut mutation_checks, mutation);
            }
            if spec.production == Production::RepeatedIdentical {
                increment(&mut mutation_checks, "deduplicated-reuse");
            }
            if spec.production == Production::DistinctSpecializations {
                increment(&mut mutation_checks, "distinct-specialization");
            }
        } else {
            let error = match result {
                Ok(()) => panic!("{}: negative generated case admitted", spec.id),
                Err(error) => error,
            };
            let expected = built.expected_error.expect("negative error class");
            assert!(
                expected.matches(&error),
                "{}: expected {expected:?}, got {error:?}",
                spec.id
            );
            assert_eq!(
                environment_snapshot(&kernel),
                before,
                "{}: rollback",
                spec.id
            );
            increment(&mut outcomes, "reject");
            increment(&mut errors, expected.label());
            increment(&mut mutation_checks, "typed-rejection-rollback");
        }
    }

    for required in ["1", "2", "3"] {
        assert!(outer_groups.contains_key(required));
        assert!(container_groups.contains_key(required));
        assert!(container_params.contains_key(required));
        assert!(nested_apps.contains_key(required));
    }
    for required in ["0", "1", "2"] {
        assert!(container_indices.contains_key(required));
    }
    for required in ["0", "1", "2", "3"] {
        assert!(constructors.contains_key(required));
    }
    for required in ["0", "1", "2", "3", "4", "5"] {
        assert!(fields.contains_key(required));
    }
    for required in ["0", "1", "2"] {
        assert!(source_owners.contains_key(required));
        assert!(container_owners.contains_key(required));
        assert!(active_parameter_slots.contains_key(required));
    }
    for required in ["0", "1", "2", "3"] {
        assert!(filler_positions.contains_key(required));
    }
    for required in ["Default", "Implicit", "StrictImplicit"] {
        assert!(binder_infos.contains_key(required));
    }
    for required in [
        "foreign-head",
        "incomplete-parameter-prefix",
        "loose-parameter",
        "negative-specialized-parameter",
        "wrong-fixed-source-parameter",
        "malformed-container-index-arity",
        "unregistered-generic",
        "unregistered-constructor-metadata",
        "unregistered-recursion-metadata",
        "unregistered-index-metadata",
        "expansion-limit-sentinel",
        "late-public-rec-1-collision",
        "wrong-universe-arity-one",
        "wrong-universe-arity-two",
    ] {
        assert!(negative_subtypes.contains_key(required));
    }
    assert_eq!(outcomes.get("admit"), Some(&320));
    assert_eq!(outcomes.get("reject"), Some(&320));

    format!(
        "schema=axeyum-lean-nested-inductive-grammar-v1\n\
seed={GENERATOR_SEED:016x}\n\
cases={}\n\
outcomes={}\n\
errors={}\n\
productions={}\n\
outer-group-sizes={}\n\
container-group-sizes={}\n\
outer-parameter-profiles={}\n\
container-parameter-counts={}\n\
container-index-counts={}\n\
constructors-per-family={}\n\
fields-per-selected-constructor={}\n\
nested-applications={}\n\
nested-depths={}\n\
result-sorts={}\n\
recursive-target-classes={}\n\
shape-variants={}\n\
index-variants={}\n\
source-owner-indices={}\n\
container-owner-indices={}\n\
active-parameter-slots={}\n\
binder-infos={}\n\
negative-subtypes={}\n\
shallow-filler-positions={}\n\
published-auxiliary-counts={}\n\
public-recursor-dependency-edges={}\n\
iota-checks={}\n\
mutation-checks={}\n\
descriptor-fnv1a64={:016x}\n",
        specs.len(),
        render_counts(&outcomes),
        render_counts(&errors),
        render_counts(&productions),
        render_counts(&outer_groups),
        render_counts(&container_groups),
        render_counts(&outer_params),
        render_counts(&container_params),
        render_counts(&container_indices),
        render_counts(&constructors),
        render_counts(&fields),
        render_counts(&nested_apps),
        render_counts(&depths),
        render_counts(&sorts),
        render_counts(&targets),
        render_counts(&shape_variants),
        render_counts(&index_variants),
        render_counts(&source_owners),
        render_counts(&container_owners),
        render_counts(&active_parameter_slots),
        render_counts(&binder_infos),
        render_counts(&negative_subtypes),
        render_counts(&filler_positions),
        render_counts(&auxiliary_counts),
        render_counts(&dependency_edges),
        render_counts(&iota_checks),
        render_counts(&mutation_checks),
        fnv1a64(&descriptors),
    )
}

#[test]
fn generated_nested_inductive_grammar_is_complete_and_byte_identical() {
    let first = run_generated_grammar();
    let second = run_generated_grammar();
    assert_eq!(
        first, second,
        "fixed-seed summary must repeat byte-for-byte"
    );
    assert_eq!(first, EXPECTED_GENERATED_SUMMARY);
}
