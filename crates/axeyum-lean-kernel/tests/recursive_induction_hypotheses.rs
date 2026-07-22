//! Native TL2.12 recursive-induction-hypothesis contract (ADR-0353).
//!
//! These tests use only the public kernel admission path. Expected recursor
//! shape and iota results are derived from the test production records, never
//! from the generated declaration under test.
#![allow(clippy::too_many_arguments, clippy::too_many_lines)]

use std::collections::BTreeSet;

use axeyum_lean_kernel::{BinderInfo, Declaration, ExprId, ExprNode, Kernel, KernelError, NameId};

const GENERATOR_SEED: u64 = 0x4158_5249_485F_4D32;
const EXPECTED_GENERATED_SUMMARY: &str = "schema=axeyum-lean-recursive-ih-grammar-v1\n\
seed=41585249485f4d32\n\
cases=768\n\
recursive-fields=0:288,1:224,2:160,3:96\n\
profiles=0p0i:192,1p0i:192,1p1i:192,2p1i:192\n\
sorts=type:384,prop:384\n\
depths=0:192,1:192,2:192,3:192\n\
index-productions=none:384,constant:320,field-dependent:64\n\
descriptor-fnv1a64=0d245921566be735\n";

#[derive(Clone, Copy, Debug)]
enum Profile {
    P0I0,
    P1I0,
    P1I1,
    P2I1,
}

impl Profile {
    const ALL: [Self; 4] = [Self::P0I0, Self::P1I0, Self::P1I1, Self::P2I1];

    const fn label(self) -> &'static str {
        match self {
            Self::P0I0 => "0p0i",
            Self::P1I0 => "1p0i",
            Self::P1I1 => "1p1i",
            Self::P2I1 => "2p1i",
        }
    }

    const fn num_params(self) -> usize {
        match self {
            Self::P0I0 => 0,
            Self::P1I0 | Self::P1I1 => 1,
            Self::P2I1 => 2,
        }
    }

    const fn num_indices(self) -> usize {
        match self {
            Self::P0I0 | Self::P1I0 => 0,
            Self::P1I1 | Self::P2I1 => 1,
        }
    }
}

#[derive(Clone, Copy, Debug)]
struct RecursiveSpec {
    position: usize,
    depth: usize,
    info: BinderInfo,
    let_wrapped: bool,
}

#[derive(Clone, Debug)]
struct CaseSpec {
    id: String,
    profile: Profile,
    prop: bool,
    total_fields: usize,
    recursive: Vec<RecursiveSpec>,
    dependent_index_for: Option<usize>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum NativeMutation {
    OmitIh,
    IhBeforeFields,
    DropIndex,
    ConstructorIndex,
    MotiveOnUnappliedField,
    OmitNestedLambda,
    NestedBinderInfo,
    NeighborField,
    WrongMotive,
}

impl NativeMutation {
    const fn id(self) -> &'static str {
        match self {
            Self::OmitIh => "omit-duplicate-reorder-ih",
            Self::IhBeforeFields => "ih-before-fields",
            Self::DropIndex => "drop-reorder-index",
            Self::ConstructorIndex => "constructor-index-for-recursive-index",
            Self::MotiveOnUnappliedField => "motive-on-unapplied-field",
            Self::OmitNestedLambda => "nested-lambda-or-argument-order",
            Self::NestedBinderInfo => "nested-binder-type-or-info",
            Self::NeighborField => "neighbor-field-recursion",
            Self::WrongMotive => "wrong-motive-or-universe",
        }
    }
}

fn sort_one(kernel: &mut Kernel) -> ExprId {
    let zero = kernel.level_zero();
    let one = kernel.level_succ(zero);
    kernel.sort(one)
}

fn family_type(kernel: &mut Kernel, profile: Profile, prop: bool, binder: NameId) -> ExprId {
    let mut ty = if prop {
        kernel.sort_zero()
    } else {
        sort_one(kernel)
    };
    if profile.num_indices() == 1 {
        let domain = sort_one(kernel);
        ty = kernel.pi(binder, domain, ty, BinderInfo::Default);
    }
    for _ in 0..profile.num_params() {
        let domain = sort_one(kernel);
        ty = kernel.pi(binder, domain, ty, BinderInfo::Default);
    }
    ty
}

/// Build `I params [Sort 0]` in a constructor context containing all params
/// followed by `preceding_fields` field binders.
fn family_application(
    kernel: &mut Kernel,
    family: ExprId,
    profile: Profile,
    preceding_fields: usize,
) -> ExprId {
    family_application_at(kernel, family, profile, preceding_fields, None)
}

fn family_application_at(
    kernel: &mut Kernel,
    family: ExprId,
    profile: Profile,
    preceding_fields: usize,
    index: Option<ExprId>,
) -> ExprId {
    let mut app = family;
    let num_params = profile.num_params();
    for parameter in 0..num_params {
        let depth = preceding_fields + num_params - parameter - 1;
        let value = kernel.bvar(u32::try_from(depth).expect("small generated depth"));
        app = kernel.app(app, value);
    }
    if profile.num_indices() == 1 {
        let index = index.unwrap_or_else(|| kernel.sort_zero());
        app = kernel.app(app, index);
    }
    app
}

fn wrap_recursive_telescope(
    kernel: &mut Kernel,
    binder: NameId,
    mut tail: ExprId,
    recursive: RecursiveSpec,
) -> ExprId {
    for _ in 0..recursive.depth {
        tail = kernel.lift_loose_bvars(tail, 0, 1);
        let domain = kernel.sort_zero();
        tail = kernel.pi(binder, domain, tail, recursive.info);
    }
    if recursive.let_wrapped {
        let body = kernel.lift_loose_bvars(tail, 0, 1);
        let declared_type = sort_one(kernel);
        let value = kernel.sort_zero();
        tail = kernel.let_(binder, declared_type, value, body);
    }
    tail
}

fn constructor_type(
    kernel: &mut Kernel,
    family: ExprId,
    profile: Profile,
    binder: NameId,
    fields: &[ExprId],
) -> ExprId {
    let mut ty = family_application(kernel, family, profile, fields.len());
    for &field in fields.iter().rev() {
        ty = kernel.pi(binder, field, ty, BinderInfo::Default);
    }
    for _ in 0..profile.num_params() {
        let domain = sort_one(kernel);
        ty = kernel.pi(binder, domain, ty, BinderInfo::Default);
    }
    ty
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

fn apply_recursor(
    kernel: &mut Kernel,
    recursor: NameId,
    levels: &[axeyum_lean_kernel::LevelId],
    params: &[ExprId],
    motive: ExprId,
    minor: ExprId,
    indexed: bool,
    major_index: ExprId,
    major: ExprId,
) -> ExprId {
    let mut app = kernel.const_(recursor, levels.to_vec());
    for &parameter in params {
        app = kernel.app(app, parameter);
    }
    app = kernel.app(app, motive);
    app = kernel.app(app, minor);
    if indexed {
        app = kernel.app(app, major_index);
    }
    kernel.app(app, major)
}

fn expected_recursive_value(
    kernel: &mut Kernel,
    recursor: NameId,
    levels: &[axeyum_lean_kernel::LevelId],
    params: &[ExprId],
    motive: ExprId,
    minor: ExprId,
    indexed: bool,
    recursive_index: ExprId,
    field: ExprId,
    recursive: RecursiveSpec,
    binder: NameId,
) -> ExprId {
    let mut applied = field;
    for argument in (0..recursive.depth).rev() {
        let value = kernel.bvar(u32::try_from(argument).expect("small generated depth"));
        applied = kernel.app(applied, value);
    }
    let mut body = apply_recursor(
        kernel,
        recursor,
        levels,
        params,
        motive,
        minor,
        indexed,
        recursive_index,
        applied,
    );
    for _ in 0..recursive.depth {
        let domain = kernel.sort_zero();
        body = kernel.lam(binder, domain, body, recursive.info);
    }
    body
}

fn apply_all(kernel: &mut Kernel, mut head: ExprId, arguments: &[ExprId]) -> ExprId {
    for &argument in arguments {
        head = kernel.app(head, argument);
    }
    head
}

fn applicable_mutations(spec: &CaseSpec) -> Vec<NativeMutation> {
    if spec.recursive.is_empty() {
        return Vec::new();
    }
    let mut mutations = vec![
        NativeMutation::OmitIh,
        NativeMutation::IhBeforeFields,
        NativeMutation::WrongMotive,
    ];
    if spec.profile.num_indices() > 0 {
        mutations.push(NativeMutation::DropIndex);
        mutations.push(NativeMutation::ConstructorIndex);
    }
    if spec.recursive.iter().any(|recursive| recursive.depth > 0) {
        mutations.push(NativeMutation::MotiveOnUnappliedField);
        mutations.push(NativeMutation::OmitNestedLambda);
        mutations.push(NativeMutation::NestedBinderInfo);
    }
    if spec.total_fields > spec.recursive.len() {
        mutations.push(NativeMutation::NeighborField);
    }
    mutations
}

#[allow(clippy::too_many_arguments)]
fn mutated_recursive_value(
    kernel: &mut Kernel,
    mutation: NativeMutation,
    recursor: NameId,
    levels: &[axeyum_lean_kernel::LevelId],
    params: &[ExprId],
    motive: ExprId,
    minor: ExprId,
    indexed: bool,
    expected_index: ExprId,
    field: ExprId,
    neighbor: ExprId,
    recursive: RecursiveSpec,
    binder: NameId,
) -> ExprId {
    let wrong_index = kernel.fvar(9_001);
    let wrong_motive = kernel.fvar(9_002);
    let selected_field = if mutation == NativeMutation::NeighborField {
        neighbor
    } else {
        field
    };
    let mut applied = selected_field;
    for argument in (0..recursive.depth).rev() {
        let value = kernel.bvar(u32::try_from(argument).expect("small generated depth"));
        applied = kernel.app(applied, value);
    }
    if mutation == NativeMutation::MotiveOnUnappliedField {
        applied = selected_field;
    }
    let recursive_index = if mutation == NativeMutation::ConstructorIndex {
        wrong_index
    } else {
        expected_index
    };
    let mut body = apply_recursor(
        kernel,
        recursor,
        levels,
        params,
        if mutation == NativeMutation::WrongMotive {
            wrong_motive
        } else {
            motive
        },
        minor,
        indexed && mutation != NativeMutation::DropIndex,
        recursive_index,
        applied,
    );
    let retained_depth = if mutation == NativeMutation::OmitNestedLambda {
        recursive.depth.saturating_sub(1)
    } else {
        recursive.depth
    };
    let binder_info = if mutation == NativeMutation::NestedBinderInfo {
        match recursive.info {
            BinderInfo::Default => BinderInfo::Implicit,
            BinderInfo::Implicit | BinderInfo::StrictImplicit | BinderInfo::InstImplicit => {
                BinderInfo::Default
            }
        }
    } else {
        recursive.info
    };
    for _ in 0..retained_depth {
        let domain = kernel.sort_zero();
        body = kernel.lam(binder, domain, body, binder_info);
    }
    body
}

fn assert_minor_shape(kernel: &Kernel, recursor_type: ExprId, spec: &CaseSpec) {
    let mut cursor = recursor_type;
    for _ in 0..=spec.profile.num_params() {
        let ExprNode::Pi(_, _, body, _) = kernel.expr_node(cursor) else {
            panic!("{}: recursor prefix ended before its minor", spec.id);
        };
        cursor = *body;
    }
    let ExprNode::Pi(_, minor_type, _, _) = kernel.expr_node(cursor) else {
        panic!("{}: recursor is missing its minor", spec.id);
    };
    cursor = *minor_type;
    for _ in 0..spec.total_fields {
        let ExprNode::Pi(_, _, body, _) = kernel.expr_node(cursor) else {
            panic!("{}: minor lost an original field", spec.id);
        };
        cursor = *body;
    }
    for recursive in &spec.recursive {
        let ExprNode::Pi(_, ih_type, body, info) = kernel.expr_node(cursor) else {
            panic!("{}: minor lost an induction hypothesis", spec.id);
        };
        assert_eq!(*info, BinderInfo::Default, "{}: IH binder", spec.id);
        let mut ih_cursor = *ih_type;
        for _ in 0..recursive.depth {
            let ExprNode::Pi(_, _, ih_body, ih_info) = kernel.expr_node(ih_cursor) else {
                panic!("{}: IH telescope is too short", spec.id);
            };
            assert_eq!(*ih_info, recursive.info, "{}: nested binder info", spec.id);
            ih_cursor = *ih_body;
        }
        assert!(
            !matches!(kernel.expr_node(ih_cursor), ExprNode::Pi(..)),
            "{}: IH telescope is too long",
            spec.id
        );
        cursor = *body;
    }
    assert!(
        !matches!(kernel.expr_node(cursor), ExprNode::Pi(..)),
        "{}: minor has unregistered trailing binders",
        spec.id
    );
}

fn assert_dependent_minor_shape(
    kernel: &Kernel,
    recursor_type: ExprId,
    profile: Profile,
    total_fields: usize,
    id: &str,
) {
    let mut cursor = recursor_type;
    for _ in 0..=profile.num_params() {
        let ExprNode::Pi(_, _, body, _) = kernel.expr_node(cursor) else {
            panic!("{id}: recursor prefix ended before its minor");
        };
        cursor = *body;
    }
    let ExprNode::Pi(_, minor_type, _, _) = kernel.expr_node(cursor) else {
        panic!("{id}: missing minor");
    };
    cursor = *minor_type;
    for _ in 0..total_fields {
        let ExprNode::Pi(_, _, body, _) = kernel.expr_node(cursor) else {
            panic!("{id}: minor lost an original field");
        };
        cursor = *body;
    }
    let ExprNode::Pi(_, ih_type, body, ih_info) = kernel.expr_node(cursor) else {
        panic!("{id}: missing dependent IH");
    };
    assert_eq!(*ih_info, BinderInfo::Default, "{id}: IH binder");
    let ExprNode::Pi(_, _, inner, outer_info) = kernel.expr_node(*ih_type) else {
        panic!("{id}: missing outer IH binder");
    };
    assert_eq!(
        *outer_info,
        BinderInfo::StrictImplicit,
        "{id}: outer binder"
    );
    let ExprNode::Pi(_, _, tail, inner_info) = kernel.expr_node(*inner) else {
        panic!("{id}: missing inner IH binder");
    };
    assert_eq!(*inner_info, BinderInfo::Implicit, "{id}: inner binder");
    assert!(!matches!(kernel.expr_node(*tail), ExprNode::Pi(..)), "{id}");
    assert!(!matches!(kernel.expr_node(*body), ExprNode::Pi(..)), "{id}");
}

fn run_positive_case(spec: &CaseSpec) -> Option<&'static str> {
    let mut kernel = Kernel::new();
    let anon = kernel.anon();
    let namespace = kernel.name_str(anon, &spec.id);
    let binder = kernel.name_str(namespace, "x");
    let family_name = kernel.name_str(namespace, "I");
    let constructor_name = kernel.name_str(family_name, "mk");
    let family = kernel.const_(family_name, vec![]);
    let ty = family_type(&mut kernel, spec.profile, spec.prop, binder);

    let mut recursive_by_position = vec![None; spec.total_fields];
    for &recursive in &spec.recursive {
        assert!(recursive.position < spec.total_fields, "{}", spec.id);
        assert!(
            recursive_by_position[recursive.position]
                .replace(recursive)
                .is_none(),
            "{}: duplicate recursive position",
            spec.id
        );
    }
    let mut fields = Vec::with_capacity(spec.total_fields);
    for (position, recursive) in recursive_by_position.into_iter().enumerate() {
        let field = if let Some(recursive) = recursive {
            let recursive_index = if spec.dependent_index_for == Some(position) {
                assert!(position > 0, "{}: dependent index needs a field", spec.id);
                Some(kernel.bvar(0))
            } else {
                None
            };
            let tail =
                family_application_at(&mut kernel, family, spec.profile, position, recursive_index);
            wrap_recursive_telescope(&mut kernel, binder, tail, recursive)
        } else if spec.dependent_index_for == Some(position + 1) {
            sort_one(&mut kernel)
        } else {
            kernel.sort_zero()
        };
        fields.push(field);
    }
    let constructor_ty = constructor_type(&mut kernel, family, spec.profile, binder, &fields);
    kernel
        .add_inductive(
            family_name,
            &[],
            spec.profile.num_params(),
            ty,
            &[(constructor_name, constructor_ty)],
        )
        .unwrap_or_else(|error| panic!("{}: admission failed: {error:?}", spec.id));

    let recursor_name = kernel.name_str(family_name, "rec");
    let declaration = kernel
        .environment()
        .get(recursor_name)
        .unwrap_or_else(|| panic!("{}: missing recursor", spec.id))
        .clone();
    let (recursor_type, rules) = match &declaration {
        Declaration::Recursor {
            ty,
            rec_rules,
            num_motives,
            num_minors,
            num_params,
            num_indices,
            ..
        } => {
            assert_eq!((*num_motives, *num_minors), (1, 1), "{}", spec.id);
            assert_eq!(
                usize::from(*num_params),
                spec.profile.num_params(),
                "{}",
                spec.id
            );
            assert_eq!(
                usize::from(*num_indices),
                spec.profile.num_indices(),
                "{}",
                spec.id
            );
            (*ty, rec_rules.clone())
        }
        _ => panic!("{}: generated declaration is not a recursor", spec.id),
    };
    assert_eq!(rules.len(), 1, "{}", spec.id);
    assert_eq!(rules[0].ctor_name, constructor_name, "{}", spec.id);
    assert_eq!(
        usize::from(rules[0].num_fields),
        spec.total_fields,
        "{}",
        spec.id
    );
    let inferred = kernel
        .infer(recursor_type)
        .unwrap_or_else(|error| panic!("{}: recursor type failed inference: {error:?}", spec.id));
    assert!(
        matches!(kernel.expr_node(inferred), ExprNode::Sort(_)),
        "{}",
        spec.id
    );
    assert_minor_shape(&kernel, recursor_type, spec);

    let levels = recursor_levels(&mut kernel, &declaration);
    let params: Vec<_> = (0..spec.profile.num_params())
        .map(|offset| kernel.fvar(100 + u64::try_from(offset).unwrap()))
        .collect();
    let motive = kernel.fvar(120);
    let minor = kernel.fvar(121);
    let runtime_fields: Vec<_> = (0..spec.total_fields)
        .map(|offset| kernel.fvar(200 + u64::try_from(offset).unwrap()))
        .collect();
    let constructor = kernel.const_(constructor_name, vec![]);
    let mut major = constructor;
    for &parameter in &params {
        major = kernel.app(major, parameter);
    }
    for &field in &runtime_fields {
        major = kernel.app(major, field);
    }
    let index = kernel.sort_zero();
    let application = apply_recursor(
        &mut kernel,
        recursor_name,
        &levels,
        &params,
        motive,
        minor,
        spec.profile.num_indices() == 1,
        index,
        major,
    );
    let fields_applied = apply_all(&mut kernel, minor, &runtime_fields);
    let mut induction_hypotheses = Vec::with_capacity(spec.recursive.len());
    for recursive in &spec.recursive {
        let recursive_index = spec
            .dependent_index_for
            .filter(|&position| position == recursive.position)
            .map_or(index, |_| runtime_fields[recursive.position - 1]);
        let ih = expected_recursive_value(
            &mut kernel,
            recursor_name,
            &levels,
            &params,
            motive,
            minor,
            spec.profile.num_indices() == 1,
            recursive_index,
            runtime_fields[recursive.position],
            *recursive,
            binder,
        );
        induction_hypotheses.push(ih);
    }
    let expected = apply_all(&mut kernel, fields_applied, &induction_hypotheses);
    let actual = kernel.whnf(application);
    assert_eq!(actual, expected, "{}: iota result", spec.id);

    let applicable = applicable_mutations(spec);
    if applicable.is_empty() {
        return None;
    }
    let mutation = applicable
        [usize::try_from(fnv1a(GENERATOR_SEED, spec.id.as_bytes())).unwrap() % applicable.len()];
    let mutated = match mutation {
        NativeMutation::OmitIh => {
            apply_all(&mut kernel, fields_applied, &induction_hypotheses[1..])
        }
        NativeMutation::IhBeforeFields => {
            let head = kernel.app(minor, induction_hypotheses[0]);
            let fields_then_ihs = apply_all(&mut kernel, head, &runtime_fields);
            apply_all(&mut kernel, fields_then_ihs, &induction_hypotheses[1..])
        }
        mutation => {
            let target = spec
                .recursive
                .iter()
                .position(|recursive| match mutation {
                    NativeMutation::MotiveOnUnappliedField
                    | NativeMutation::OmitNestedLambda
                    | NativeMutation::NestedBinderInfo => recursive.depth > 0,
                    NativeMutation::NeighborField => (0..spec.total_fields).any(|position| {
                        !spec.recursive.iter().any(|item| item.position == position)
                    }),
                    _ => true,
                })
                .expect("applicable mutation has a target recursive field");
            let recursive = spec.recursive[target];
            let expected_index = spec
                .dependent_index_for
                .filter(|&position| position == recursive.position)
                .map_or(index, |_| runtime_fields[recursive.position - 1]);
            let neighbor = (0..spec.total_fields)
                .find(|&position| !spec.recursive.iter().any(|item| item.position == position))
                .map_or(runtime_fields[recursive.position], |position| {
                    runtime_fields[position]
                });
            let mutant_ih = mutated_recursive_value(
                &mut kernel,
                mutation,
                recursor_name,
                &levels,
                &params,
                motive,
                minor,
                spec.profile.num_indices() == 1,
                expected_index,
                runtime_fields[recursive.position],
                neighbor,
                recursive,
                binder,
            );
            let mut mutant_ihs = induction_hypotheses.clone();
            mutant_ihs[target] = mutant_ih;
            apply_all(&mut kernel, fields_applied, &mutant_ihs)
        }
    };
    assert_ne!(
        actual,
        mutated,
        "{}: mutation {} survived",
        spec.id,
        mutation.id()
    );
    Some(mutation.id())
}

fn dependent_family_application(
    kernel: &mut Kernel,
    family: ExprId,
    profile: Profile,
    preceding_fields: usize,
    nested_depth: usize,
    index: ExprId,
) -> ExprId {
    let mut app = family;
    let num_params = profile.num_params();
    for parameter in 0..num_params {
        let depth = preceding_fields + nested_depth + num_params - parameter - 1;
        let value = kernel.bvar(u32::try_from(depth).expect("small dependent depth"));
        app = kernel.app(app, value);
    }
    kernel.app(app, index)
}

fn run_dependent_index_case(id: &str, profile: Profile, prop: bool, preceding_field: bool) {
    assert_eq!(profile.num_indices(), 1);
    let mut kernel = Kernel::new();
    let anon = kernel.anon();
    let namespace = kernel.name_str(anon, id);
    let binder = kernel.name_str(namespace, "x");
    let family_name = kernel.name_str(namespace, "I");
    let constructor_name = kernel.name_str(family_name, "mk");
    let family = kernel.const_(family_name, vec![]);
    let ty = family_type(&mut kernel, profile, prop, binder);
    let recursive_position = usize::from(preceding_field);

    // field : (a : Sort 1) -> (b : a) -> I params a
    let recursive_field = {
        let a_under_two = kernel.bvar(1);
        let tail = dependent_family_application(
            &mut kernel,
            family,
            profile,
            recursive_position,
            2,
            a_under_two,
        );
        let a_for_b_domain = kernel.bvar(0);
        let inner = kernel.pi(binder, a_for_b_domain, tail, BinderInfo::Implicit);
        let a_domain = sort_one(&mut kernel);
        kernel.pi(binder, a_domain, inner, BinderInfo::StrictImplicit)
    };
    let mut fields = Vec::new();
    if preceding_field {
        fields.push(kernel.sort_zero());
    }
    fields.push(recursive_field);
    let constructor_ty = constructor_type(&mut kernel, family, profile, binder, &fields);
    kernel
        .add_inductive(
            family_name,
            &[],
            profile.num_params(),
            ty,
            &[(constructor_name, constructor_ty)],
        )
        .unwrap_or_else(|error| panic!("{id}: admission failed: {error:?}"));

    let recursor_name = kernel.name_str(family_name, "rec");
    let declaration = kernel.environment().get(recursor_name).unwrap().clone();
    let (recursor_type, recursor_fields) = match &declaration {
        Declaration::Recursor {
            ty,
            rec_rules,
            num_indices,
            ..
        } => {
            assert_eq!(*num_indices, 1, "{id}");
            assert_eq!(rec_rules.len(), 1, "{id}");
            (*ty, rec_rules[0].num_fields)
        }
        _ => panic!("{id}: missing recursor"),
    };
    assert_eq!(usize::from(recursor_fields), fields.len(), "{id}");
    let inferred = kernel.infer(recursor_type).unwrap();
    assert!(
        matches!(kernel.expr_node(inferred), ExprNode::Sort(_)),
        "{id}"
    );
    assert_dependent_minor_shape(&kernel, recursor_type, profile, fields.len(), id);

    let levels = recursor_levels(&mut kernel, &declaration);
    let params: Vec<_> = (0..profile.num_params())
        .map(|offset| kernel.fvar(100 + u64::try_from(offset).unwrap()))
        .collect();
    let motive = kernel.fvar(120);
    let minor = kernel.fvar(121);
    let first = kernel.fvar(200);
    let recursive_value = kernel.fvar(200 + u64::from(preceding_field));
    let constructor = kernel.const_(constructor_name, vec![]);
    let mut major = constructor;
    for &parameter in &params {
        major = kernel.app(major, parameter);
    }
    if preceding_field {
        major = kernel.app(major, first);
    }
    major = kernel.app(major, recursive_value);
    let result_index = kernel.sort_zero();
    let application = apply_recursor(
        &mut kernel,
        recursor_name,
        &levels,
        &params,
        motive,
        minor,
        true,
        result_index,
        major,
    );
    let ih = {
        let a = kernel.bvar(1);
        let b = kernel.bvar(0);
        let applied = kernel.app(recursive_value, a);
        let applied = kernel.app(applied, b);
        let recursive_call = apply_recursor(
            &mut kernel,
            recursor_name,
            &levels,
            &params,
            motive,
            minor,
            true,
            a,
            applied,
        );
        let b_domain = kernel.bvar(0);
        let inner = kernel.lam(binder, b_domain, recursive_call, BinderInfo::Implicit);
        let a_domain = sort_one(&mut kernel);
        kernel.lam(binder, a_domain, inner, BinderInfo::StrictImplicit)
    };
    let mut expected = minor;
    if preceding_field {
        expected = kernel.app(expected, first);
    }
    expected = kernel.app(expected, recursive_value);
    expected = kernel.app(expected, ih);
    assert_eq!(kernel.whnf(application), expected, "{id}: dependent iota");
}

fn environment_snapshot(kernel: &Kernel) -> Vec<(NameId, Declaration)> {
    kernel
        .environment()
        .iter()
        .map(|(&name, declaration)| (name, declaration.clone()))
        .collect()
}

fn mutate_pi_domain_at(
    kernel: &mut Kernel,
    expression: ExprId,
    depth: usize,
    replacement: ExprId,
) -> ExprId {
    let (name, domain, body, info) = match kernel.expr_node(expression) {
        ExprNode::Pi(name, domain, body, info) => (*name, *domain, *body, *info),
        _ => panic!("recursor contract ended before binder {depth}"),
    };
    if depth == 0 {
        kernel.pi(name, replacement, body, info)
    } else {
        let body = mutate_pi_domain_at(kernel, body, depth - 1, replacement);
        kernel.pi(name, domain, body, info)
    }
}

fn mutation_fixture() -> (Kernel, Declaration) {
    let mut kernel = Kernel::new();
    let anon = kernel.anon();
    let namespace = kernel.name_str(anon, "mutation-contract");
    let binder = kernel.name_str(namespace, "x");
    let family_name = kernel.name_str(namespace, "I");
    let constructor_name = kernel.name_str(family_name, "mk");
    let family = kernel.const_(family_name, vec![]);
    let profile = Profile::P1I1;
    let ty = family_type(&mut kernel, profile, false, binder);
    let recursive = family_application(&mut kernel, family, profile, 0);
    let constructor_ty = constructor_type(&mut kernel, family, profile, binder, &[recursive]);
    kernel
        .add_inductive(
            family_name,
            &[],
            profile.num_params(),
            ty,
            &[(constructor_name, constructor_ty)],
        )
        .unwrap();
    let recursor_name = kernel.name_str(family_name, "rec");
    let declaration = kernel.environment().get(recursor_name).unwrap().clone();
    (kernel, declaration)
}

fn assert_negative_case(id: &str) {
    let mut kernel = Kernel::new();
    let anon = kernel.anon();
    let namespace = kernel.name_str(anon, id);
    let binder = kernel.name_str(namespace, "x");
    let family_name = kernel.name_str(namespace, "I");
    let constructor_name = kernel.name_str(family_name, "mk");
    let family = kernel.const_(family_name, vec![]);
    let before;
    let result = match id {
        "wrong-tail-params" => {
            let ty = {
                let result = sort_one(&mut kernel);
                let domain = sort_one(&mut kernel);
                kernel.pi(binder, domain, result, BinderInfo::Default)
            };
            let result = {
                let parameter = kernel.bvar(2);
                kernel.app(family, parameter)
            };
            let wrong_recursive = {
                let wrong_parameter = kernel.bvar(0);
                kernel.app(family, wrong_parameter)
            };
            let recursive = kernel.pi(binder, wrong_recursive, result, BinderInfo::Default);
            let extra_domain = sort_one(&mut kernel);
            let extra = kernel.pi(binder, extra_domain, recursive, BinderInfo::Default);
            let parameter_domain = sort_one(&mut kernel);
            let constructor_ty = kernel.pi(binder, parameter_domain, extra, BinderInfo::Default);
            before = environment_snapshot(&kernel);
            kernel.add_inductive(
                family_name,
                &[],
                1,
                ty,
                &[(constructor_name, constructor_ty)],
            )
        }
        "family-in-domain" => {
            let ty = sort_one(&mut kernel);
            let result = family;
            let function_result = kernel.sort_zero();
            let function = kernel.pi(binder, family, function_result, BinderInfo::Default);
            let constructor_ty = kernel.pi(binder, function, result, BinderInfo::Default);
            before = environment_snapshot(&kernel);
            kernel.add_inductive(
                family_name,
                &[],
                0,
                ty,
                &[(constructor_name, constructor_ty)],
            )
        }
        "family-in-index" => {
            let index_domain = sort_one(&mut kernel);
            let result_sort = sort_one(&mut kernel);
            let ty = kernel.pi(binder, index_domain, result_sort, BinderInfo::Default);
            let base_index = kernel.sort_zero();
            let recursive_index = kernel.app(family, base_index);
            let invalid_field = kernel.app(family, recursive_index);
            let result_index = kernel.sort_zero();
            let result = kernel.app(family, result_index);
            let constructor_ty = kernel.pi(binder, invalid_field, result, BinderInfo::Default);
            before = environment_snapshot(&kernel);
            kernel.add_inductive(
                family_name,
                &[],
                0,
                ty,
                &[(constructor_name, constructor_ty)],
            )
        }
        "nested-foreign-head" => {
            let wrapper_name = kernel.name_str(namespace, "F");
            let wrapper = kernel.const_(wrapper_name, vec![]);
            let wrapper_ty = {
                let domain = sort_one(&mut kernel);
                let result = sort_one(&mut kernel);
                kernel.pi(binder, domain, result, BinderInfo::Default)
            };
            kernel
                .add_declaration(Declaration::Axiom {
                    name: wrapper_name,
                    uparams: vec![],
                    ty: wrapper_ty,
                })
                .unwrap();
            let ty = sort_one(&mut kernel);
            let nested = kernel.app(wrapper, family);
            let constructor_ty = kernel.pi(binder, nested, family, BinderInfo::Default);
            before = environment_snapshot(&kernel);
            kernel.add_inductive(
                family_name,
                &[],
                0,
                ty,
                &[(constructor_name, constructor_ty)],
            )
        }
        _ => panic!("unknown negative case {id}"),
    };
    let error = result.expect_err(id);
    match id {
        "family-in-domain" => assert!(matches!(
            error,
            KernelError::NonPositiveInductiveOccurrence { field_index: 0, .. }
        )),
        "wrong-tail-params" | "family-in-index" | "nested-foreign-head" => assert!(matches!(
            error,
            KernelError::InvalidInductiveOccurrence { .. }
        )),
        _ => unreachable!(),
    }
    assert_eq!(environment_snapshot(&kernel), before, "{id}: rollback");
}

fn fnv1a(mut digest: u64, bytes: &[u8]) -> u64 {
    for &byte in bytes {
        digest ^= u64::from(byte);
        digest = digest.wrapping_mul(0x0000_0100_0000_01b3);
    }
    digest
}

fn generated_recursive_specs(
    total_fields: usize,
    depth: usize,
    variant: usize,
) -> Vec<RecursiveSpec> {
    let count = total_fields.min(variant.min(3));
    let info = match variant {
        0 | 1 => BinderInfo::Default,
        2 => BinderInfo::Implicit,
        _ => BinderInfo::StrictImplicit,
    };
    (0..count)
        .map(|offset| RecursiveSpec {
            position: if variant == 1 {
                total_fields - 1
            } else {
                offset
            },
            depth,
            info,
            let_wrapped: variant == 3 && (offset + depth).is_multiple_of(2),
        })
        .collect()
}

fn run_generated_grammar() -> String {
    let mut ids = BTreeSet::new();
    let mut mutations = BTreeSet::new();
    let mut digest = 0xcbf2_9ce4_8422_2325_u64;
    let mut cases = 0_usize;
    let mut recursive_counts = [0_usize; 4];
    let mut profile_counts = [0_usize; 4];
    let mut sort_counts = [0_usize; 2];
    let mut depth_counts = [0_usize; 4];
    let mut index_counts = [0_usize; 3];

    for (profile_index, profile) in Profile::ALL.into_iter().enumerate() {
        for (sort_index, prop) in [false, true].into_iter().enumerate() {
            for (depth, depth_count) in depth_counts.iter_mut().enumerate() {
                for total_fields in 0..=5 {
                    for variant in 0..=3 {
                        let recursive = generated_recursive_specs(total_fields, depth, variant);
                        let dependent_index_for =
                            (profile.num_indices() == 1 && variant == 1 && total_fields >= 2)
                                .then(|| recursive[0].position);
                        let index_kind = if profile.num_indices() == 0 {
                            index_counts[0] += 1;
                            "none"
                        } else if dependent_index_for.is_some() {
                            index_counts[2] += 1;
                            "field-dependent"
                        } else {
                            index_counts[1] += 1;
                            "constant"
                        };
                        let id = format!(
                            "generated_{}_{}_d{depth}_f{total_fields}_v{variant}",
                            profile.label(),
                            if prop { "prop" } else { "type" }
                        );
                        assert!(ids.insert(id.clone()), "duplicate generated identity: {id}");
                        let descriptor = format!(
                            "{id}|{}|{}|{depth}|{total_fields}|{variant}|{}|{index_kind}\n",
                            profile.label(),
                            if prop { "prop" } else { "type" },
                            recursive.len()
                        );
                        digest = fnv1a(digest, descriptor.as_bytes());
                        if let Some(mutation) = run_positive_case(&CaseSpec {
                            id,
                            profile,
                            prop,
                            total_fields,
                            recursive: recursive.clone(),
                            dependent_index_for,
                        }) {
                            mutations.insert(mutation);
                        }
                        cases += 1;
                        recursive_counts[recursive.len()] += 1;
                        profile_counts[profile_index] += 1;
                        sort_counts[sort_index] += 1;
                        *depth_count += 1;
                    }
                }
            }
        }
    }

    assert_eq!(cases, 768);
    assert_eq!(ids.len(), cases);
    assert!(recursive_counts.iter().all(|&count| count > 0));
    assert_eq!(
        mutations,
        BTreeSet::from([
            "constructor-index-for-recursive-index",
            "drop-reorder-index",
            "ih-before-fields",
            "motive-on-unapplied-field",
            "neighbor-field-recursion",
            "nested-binder-type-or-info",
            "nested-lambda-or-argument-order",
            "omit-duplicate-reorder-ih",
            "wrong-motive-or-universe",
        ])
    );
    format!(
        "schema=axeyum-lean-recursive-ih-grammar-v1\n\
         seed={GENERATOR_SEED:016x}\n\
         cases={cases}\n\
         recursive-fields=0:{},1:{},2:{},3:{}\n\
         profiles=0p0i:{},1p0i:{},1p1i:{},2p1i:{}\n\
         sorts=type:{},prop:{}\n\
         depths=0:{},1:{},2:{},3:{}\n\
         index-productions=none:{},constant:{},field-dependent:{}\n\
         descriptor-fnv1a64={digest:016x}\n",
        recursive_counts[0],
        recursive_counts[1],
        recursive_counts[2],
        recursive_counts[3],
        profile_counts[0],
        profile_counts[1],
        profile_counts[2],
        profile_counts[3],
        sort_counts[0],
        sort_counts[1],
        depth_counts[0],
        depth_counts[1],
        depth_counts[2],
        depth_counts[3],
        index_counts[0],
        index_counts[1],
        index_counts[2],
    )
}

#[test]
fn preregistered_positive_shape_controls_admit_and_compute() {
    let cases = [
        CaseSpec {
            id: "direct-control".into(),
            profile: Profile::P1I0,
            prop: false,
            total_fields: 1,
            recursive: generated_recursive_specs(1, 0, 1),
            dependent_index_for: None,
        },
        CaseSpec {
            id: "vector-direct-indexed".into(),
            profile: Profile::P1I1,
            prop: false,
            total_fields: 3,
            recursive: vec![RecursiveSpec {
                position: 2,
                depth: 0,
                info: BinderInfo::Default,
                let_wrapped: false,
            }],
            dependent_index_for: None,
        },
        CaseSpec {
            id: "higher-order-zero-index".into(),
            profile: Profile::P1I0,
            prop: false,
            total_fields: 1,
            recursive: generated_recursive_specs(1, 2, 1),
            dependent_index_for: None,
        },
        CaseSpec {
            id: "mixed-fields".into(),
            profile: Profile::P1I1,
            prop: false,
            total_fields: 5,
            recursive: vec![RecursiveSpec {
                position: 2,
                depth: 1,
                info: BinderInfo::Default,
                let_wrapped: false,
            }],
            dependent_index_for: None,
        },
        CaseSpec {
            id: "multiple-recursive".into(),
            profile: Profile::P2I1,
            prop: false,
            total_fields: 4,
            recursive: vec![
                RecursiveSpec {
                    position: 0,
                    depth: 0,
                    info: BinderInfo::Default,
                    let_wrapped: false,
                },
                RecursiveSpec {
                    position: 3,
                    depth: 2,
                    info: BinderInfo::Default,
                    let_wrapped: false,
                },
            ],
            dependent_index_for: None,
        },
        CaseSpec {
            id: "implicit-telescope".into(),
            profile: Profile::P1I1,
            prop: false,
            total_fields: 1,
            recursive: vec![RecursiveSpec {
                position: 0,
                depth: 2,
                info: BinderInfo::StrictImplicit,
                let_wrapped: false,
            }],
            dependent_index_for: None,
        },
        CaseSpec {
            id: "reducible-wrapper".into(),
            profile: Profile::P1I1,
            prop: false,
            total_fields: 1,
            recursive: vec![RecursiveSpec {
                position: 0,
                depth: 2,
                info: BinderInfo::Implicit,
                let_wrapped: true,
            }],
            dependent_index_for: None,
        },
        CaseSpec {
            id: "prop-acc".into(),
            profile: Profile::P2I1,
            prop: true,
            total_fields: 2,
            recursive: vec![RecursiveSpec {
                position: 1,
                depth: 2,
                info: BinderInfo::Default,
                let_wrapped: false,
            }],
            dependent_index_for: None,
        },
    ];
    for case in cases {
        let _ = run_positive_case(&case);
    }
    run_dependent_index_case("acc-indexed-dependent", Profile::P2I1, false, true);
    run_dependent_index_case("two-binder-dependent", Profile::P1I1, false, false);
}

#[test]
fn preregistered_negative_shape_controls_reject_transactionally() {
    for id in [
        "wrong-tail-params",
        "family-in-domain",
        "family-in-index",
        "nested-foreign-head",
    ] {
        assert_negative_case(id);
    }
}

#[test]
fn native_mutation_registry_rejects_recursor_contract_faults() {
    let (mut kernel, expected) = mutation_fixture();
    let mut registered: BTreeSet<_> = [
        "omit-duplicate-reorder-ih",
        "ih-before-fields",
        "drop-reorder-index",
        "constructor-index-for-recursive-index",
        "motive-on-unapplied-field",
        "nested-lambda-or-argument-order",
        "nested-binder-type-or-info",
        "neighbor-field-recursion",
        "wrong-motive-or-universe",
    ]
    .into_iter()
    .collect();

    let mut wrong_type = expected.clone();
    let mut wrong_minor_type = expected.clone();
    let mut wrong_rule = expected.clone();
    let mut wrong_nfields = expected.clone();
    let replacement = kernel.fvar(9_100);
    let Declaration::Recursor {
        ty,
        rec_rules,
        num_params,
        ..
    } = &expected
    else {
        panic!("mutation fixture did not generate a recursor");
    };
    if let Declaration::Recursor { ty, .. } = &mut wrong_type {
        *ty = replacement;
    }
    if let Declaration::Recursor { ty, .. } = &mut wrong_minor_type {
        *ty = mutate_pi_domain_at(&mut kernel, *ty, usize::from(*num_params) + 1, replacement);
    }
    if let Declaration::Recursor { rec_rules, .. } = &mut wrong_rule {
        rec_rules[0].value = replacement;
    }
    if let Declaration::Recursor { rec_rules, .. } = &mut wrong_nfields {
        rec_rules[0].num_fields += 1;
    }
    assert!(!rec_rules.is_empty());
    assert_ne!(*ty, replacement);
    for (label, candidate) in [
        ("type", wrong_type),
        ("minor-type", wrong_minor_type),
        ("rule-rhs", wrong_rule),
        ("nfields", wrong_nfields),
    ] {
        assert_ne!(
            candidate, expected,
            "official recursor {label} mutation survived"
        );
    }
    assert!(registered.insert("official-recursor-type-minor-rule-nfields"));
    assert_eq!(
        registered,
        BTreeSet::from([
            "constructor-index-for-recursive-index",
            "drop-reorder-index",
            "ih-before-fields",
            "motive-on-unapplied-field",
            "neighbor-field-recursion",
            "nested-binder-type-or-info",
            "nested-lambda-or-argument-order",
            "official-recursor-type-minor-rule-nfields",
            "omit-duplicate-reorder-ih",
            "wrong-motive-or-universe",
        ])
    );
}

#[test]
fn generated_recursive_profile_is_complete_and_byte_identical() {
    let first = run_generated_grammar();
    let second = run_generated_grammar();
    assert_eq!(first.as_bytes(), second.as_bytes());
    assert_eq!(first, EXPECTED_GENERATED_SUMMARY);
}
