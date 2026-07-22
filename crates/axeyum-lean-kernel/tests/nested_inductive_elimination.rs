//! TL2.14 M2 native nested-inductive expansion and restoration gates.

use axeyum_lean_kernel::{
    BinderInfo, Declaration, ExprId, InductiveFamilySpec, Kernel, KernelError, NameId,
};

fn sort_one(kernel: &mut Kernel) -> ExprId {
    let zero = kernel.level_zero();
    let one = kernel.level_succ(zero);
    kernel.sort(one)
}

fn declarations(kernel: &Kernel) -> Vec<Declaration> {
    kernel
        .environment()
        .iter()
        .map(|(_, declaration)| declaration.clone())
        .collect()
}

fn declare_box(kernel: &mut Kernel) -> (NameId, NameId) {
    let root = kernel.anon();
    let box_name = kernel.name_str(root, "M2Box");
    let wrap = kernel.name_str(box_name, "wrap");
    let alpha = kernel.name_str(root, "alpha");
    let value = kernel.name_str(root, "value");
    let type_ = sort_one(kernel);
    let box_type = kernel.pi(alpha, type_, type_, BinderInfo::Implicit);

    let box_const = kernel.const_(box_name, vec![]);
    let alpha_value = kernel.bvar(0);
    let result_alpha = kernel.bvar(1);
    let result = kernel.app(box_const, result_alpha);
    let fields = kernel.pi(value, alpha_value, result, BinderInfo::Default);
    let wrap_type = kernel.pi(alpha, type_, fields, BinderInfo::Implicit);
    kernel
        .add_inductive(box_name, &[], 1, box_type, &[(wrap, wrap_type)])
        .expect("one-family container admits before nested expansion");
    (box_name, wrap)
}

fn declare_prop_box(kernel: &mut Kernel) -> (NameId, NameId) {
    let root = kernel.anon();
    let box_name = kernel.name_str(root, "M2PropBox");
    let wrap = kernel.name_str(box_name, "wrap");
    let alpha = kernel.name_str(root, "alpha");
    let value = kernel.name_str(root, "value");
    let prop = kernel.sort_zero();
    let box_type = kernel.pi(alpha, prop, prop, BinderInfo::Implicit);
    let box_const = kernel.const_(box_name, vec![]);
    let alpha_value = kernel.bvar(0);
    let result_alpha = kernel.bvar(1);
    let result = kernel.app(box_const, result_alpha);
    let fields = kernel.pi(value, alpha_value, result, BinderInfo::Default);
    let wrap_type = kernel.pi(alpha, prop, fields, BinderInfo::Implicit);
    kernel
        .add_inductive(box_name, &[], 1, box_type, &[(wrap, wrap_type)])
        .expect("one-family Prop container admits before nested expansion");
    (box_name, wrap)
}

fn declare_polymorphic_box(kernel: &mut Kernel) -> (NameId, NameId, NameId) {
    let root = kernel.anon();
    let box_name = kernel.name_str(root, "M2UniverseBox");
    let wrap = kernel.name_str(box_name, "wrap");
    let universe = kernel.name_str(root, "containerUniverse");
    let alpha = kernel.name_str(root, "alpha");
    let value = kernel.name_str(root, "value");
    let level = kernel.level_param(universe);
    let sort = kernel.sort(level);
    let box_type = kernel.pi(alpha, sort, sort, BinderInfo::Implicit);
    let box_const = kernel.const_(box_name, vec![level]);
    let result_argument = kernel.bvar(1);
    let result = kernel.app(box_const, result_argument);
    let value_domain = kernel.bvar(0);
    let fields = kernel.pi(value, value_domain, result, BinderInfo::Default);
    let wrap_type = kernel.pi(alpha, sort, fields, BinderInfo::Implicit);
    kernel
        .add_inductive(box_name, &[universe], 1, box_type, &[(wrap, wrap_type)])
        .expect("universe-polymorphic container admits");
    (box_name, wrap, universe)
}

fn declare_two_parameter_container(kernel: &mut Kernel) -> NameId {
    let root = kernel.anon();
    let family = kernel.name_str(root, "M2BinaryContainer");
    let alpha = kernel.name_str(root, "alpha");
    let beta = kernel.name_str(root, "beta");
    let type_ = sort_one(kernel);
    let beta_body = kernel.pi(beta, type_, type_, BinderInfo::Implicit);
    let family_type = kernel.pi(alpha, type_, beta_body, BinderInfo::Implicit);
    kernel
        .add_inductive(family, &[], 2, family_type, &[])
        .expect("two-parameter empty container admits");
    family
}

fn declare_index_type(kernel: &mut Kernel) -> (NameId, NameId) {
    let root = kernel.anon();
    let family = kernel.name_str(root, "M2Index");
    let zero = kernel.name_str(family, "zero");
    let type_ = sort_one(kernel);
    let family_const = kernel.const_(family, vec![]);
    kernel
        .add_inductive(family, &[], 0, type_, &[(zero, family_const)])
        .expect("index enum admits");
    (family, zero)
}

fn declare_nat_like(kernel: &mut Kernel) -> (NameId, NameId, NameId) {
    let root = kernel.anon();
    let family = kernel.name_str(root, "M2ResultNat");
    let zero = kernel.name_str(family, "zero");
    let succ = kernel.name_str(family, "succ");
    let type_ = sort_one(kernel);
    let family_const = kernel.const_(family, vec![]);
    let succ_type = kernel.pi(root, family_const, family_const, BinderInfo::Default);
    kernel
        .add_inductive(
            family,
            &[],
            0,
            type_,
            &[(zero, family_const), (succ, succ_type)],
        )
        .expect("result Nat-like family admits");
    (family, zero, succ)
}

fn unfold_apps(kernel: &Kernel, mut expression: ExprId) -> (ExprId, Vec<ExprId>) {
    let mut arguments = Vec::new();
    while let axeyum_lean_kernel::ExprNode::App(function, argument) = kernel.expr_node(expression) {
        arguments.push(*argument);
        expression = *function;
    }
    arguments.reverse();
    (expression, arguments)
}

fn declare_indexed_box(kernel: &mut Kernel, index: NameId) -> (NameId, NameId) {
    let root = kernel.anon();
    let family = kernel.name_str(root, "M2IndexedBox");
    let constructor = kernel.name_str(family, "wrap");
    let alpha = kernel.name_str(root, "alpha");
    let index_name = kernel.name_str(root, "index");
    let value = kernel.name_str(root, "value");
    let type_ = sort_one(kernel);
    let index_const = kernel.const_(index, vec![]);
    let indexed_result = kernel.pi(index_name, index_const, type_, BinderInfo::Default);
    let family_type = kernel.pi(alpha, type_, indexed_result, BinderInfo::Implicit);

    let family_const = kernel.const_(family, vec![]);
    let alpha_argument = kernel.bvar(2);
    let index_argument = kernel.bvar(1);
    let result = kernel.app(family_const, alpha_argument);
    let result = kernel.app(result, index_argument);
    let value_domain = kernel.bvar(1);
    let value_field = kernel.pi(value, value_domain, result, BinderInfo::Default);
    let index_field = kernel.pi(index_name, index_const, value_field, BinderInfo::Default);
    let constructor_type = kernel.pi(alpha, type_, index_field, BinderInfo::Implicit);
    kernel
        .add_inductive(
            family,
            &[],
            1,
            family_type,
            &[(constructor, constructor_type)],
        )
        .expect("indexed container admits");
    (family, constructor)
}

fn declare_double_indexed_box(kernel: &mut Kernel, index: NameId) -> (NameId, NameId) {
    let root = kernel.anon();
    let family = kernel.name_str(root, "M2DoubleIndexedBox");
    let constructor = kernel.name_str(family, "wrap");
    let alpha = kernel.name_str(root, "alpha");
    let first_index = kernel.name_str(root, "firstIndex");
    let second_index = kernel.name_str(root, "secondIndex");
    let value = kernel.name_str(root, "value");
    let type_ = sort_one(kernel);
    let index_const = kernel.const_(index, vec![]);
    let second_indexed_result = kernel.pi(second_index, index_const, type_, BinderInfo::Default);
    let first_indexed_result = kernel.pi(
        first_index,
        index_const,
        second_indexed_result,
        BinderInfo::Default,
    );
    let family_type = kernel.pi(alpha, type_, first_indexed_result, BinderInfo::Implicit);

    let family_const = kernel.const_(family, vec![]);
    let alpha_result = kernel.bvar(3);
    let first_result = kernel.bvar(2);
    let second_result = kernel.bvar(1);
    let mut result = kernel.app(family_const, alpha_result);
    result = kernel.app(result, first_result);
    result = kernel.app(result, second_result);
    let value_domain = kernel.bvar(2);
    let value_field = kernel.pi(value, value_domain, result, BinderInfo::Default);
    let second_field = kernel.pi(second_index, index_const, value_field, BinderInfo::Default);
    let first_field = kernel.pi(first_index, index_const, second_field, BinderInfo::Default);
    let constructor_type = kernel.pi(alpha, type_, first_field, BinderInfo::Implicit);
    kernel
        .add_inductive(
            family,
            &[],
            1,
            family_type,
            &[(constructor, constructor_type)],
        )
        .expect("two-index container admits");
    (family, constructor)
}

fn declare_mutual_container(kernel: &mut Kernel) -> (NameId, NameId, NameId, NameId) {
    let root = kernel.anon();
    let left = kernel.name_str(root, "M2ContainerLeft");
    let right = kernel.name_str(root, "M2ContainerRight");
    let left_make = kernel.name_str(left, "make");
    let right_make = kernel.name_str(right, "make");
    let alpha = kernel.name_str(root, "alpha");
    let value = kernel.name_str(root, "value");
    let recursive = kernel.name_str(root, "recursive");
    let type_ = sort_one(kernel);
    let family_type = kernel.pi(alpha, type_, type_, BinderInfo::Implicit);
    let left_const = kernel.const_(left, vec![]);
    let right_const = kernel.const_(right, vec![]);

    let left_result_argument = kernel.bvar(2);
    let left_result = kernel.app(left_const, left_result_argument);
    let right_field_argument = kernel.bvar(1);
    let right_field = kernel.app(right_const, right_field_argument);
    let left_recursive = kernel.pi(recursive, right_field, left_result, BinderInfo::Default);
    let left_value_domain = kernel.bvar(0);
    let left_fields = kernel.pi(
        value,
        left_value_domain,
        left_recursive,
        BinderInfo::Default,
    );
    let left_constructor = kernel.pi(alpha, type_, left_fields, BinderInfo::Implicit);

    let right_result_argument = kernel.bvar(2);
    let right_result = kernel.app(right_const, right_result_argument);
    let left_field_argument = kernel.bvar(1);
    let left_field = kernel.app(left_const, left_field_argument);
    let right_recursive = kernel.pi(recursive, left_field, right_result, BinderInfo::Default);
    let right_value_domain = kernel.bvar(0);
    let right_fields = kernel.pi(
        value,
        right_value_domain,
        right_recursive,
        BinderInfo::Default,
    );
    let right_constructor = kernel.pi(alpha, type_, right_fields, BinderInfo::Implicit);

    let families = [
        InductiveFamilySpec::new(left, family_type, vec![(left_make, left_constructor)]),
        InductiveFamilySpec::new(right, family_type, vec![(right_make, right_constructor)]),
    ];
    kernel
        .add_mutual_inductive(&[], 1, &families)
        .expect("existing mutual container group admits");
    (left, right, left_make, right_make)
}

fn declare_container_group_with_empty_owner(kernel: &mut Kernel) -> (NameId, NameId, NameId) {
    let root = kernel.anon();
    let occupied = kernel.name_str(root, "M2OccupiedContainer");
    let empty = kernel.name_str(root, "M2EmptyContainer");
    let make = kernel.name_str(occupied, "make");
    let alpha = kernel.name_str(root, "alpha");
    let value = kernel.name_str(root, "value");
    let type_ = sort_one(kernel);
    let family_type = kernel.pi(alpha, type_, type_, BinderInfo::Implicit);
    let occupied_const = kernel.const_(occupied, vec![]);
    let result_argument = kernel.bvar(1);
    let result = kernel.app(occupied_const, result_argument);
    let value_domain = kernel.bvar(0);
    let fields = kernel.pi(value, value_domain, result, BinderInfo::Default);
    let constructor_type = kernel.pi(alpha, type_, fields, BinderInfo::Implicit);
    let families = [
        InductiveFamilySpec::new(occupied, family_type, vec![(make, constructor_type)]),
        InductiveFamilySpec::new(empty, family_type, vec![]),
    ];
    kernel
        .add_mutual_inductive(&[], 1, &families)
        .expect("container group with an empty owner admits");
    (occupied, empty, make)
}

fn declare_container_over_box(kernel: &mut Kernel, box_name: NameId) -> (NameId, NameId) {
    let root = kernel.anon();
    let family = kernel.name_str(root, "M2OuterBox");
    let make = kernel.name_str(family, "make");
    let alpha = kernel.name_str(root, "alpha");
    let contents = kernel.name_str(root, "contents");
    let type_ = sort_one(kernel);
    let family_type = kernel.pi(alpha, type_, type_, BinderInfo::Implicit);
    let family_const = kernel.const_(family, vec![]);
    let box_const = kernel.const_(box_name, vec![]);
    let box_argument = kernel.bvar(0);
    let box_alpha = kernel.app(box_const, box_argument);
    let result_argument = kernel.bvar(1);
    let result = kernel.app(family_const, result_argument);
    let fields = kernel.pi(contents, box_alpha, result, BinderInfo::Default);
    let constructor_type = kernel.pi(alpha, type_, fields, BinderInfo::Implicit);
    kernel
        .add_inductive(family, &[], 1, family_type, &[(make, constructor_type)])
        .expect("ordinary container whose field uses another container admits");
    (family, make)
}

fn assert_no_temporary_names(kernel: &Kernel) {
    for (name, declaration) in kernel.environment().iter() {
        assert!(!kernel.display_name(*name).to_string().contains("_nested"));
        let mut expressions = vec![declaration.ty()];
        if let Declaration::Recursor { rec_rules, .. } = declaration {
            expressions.extend(rec_rules.iter().map(|rule| rule.value));
        }
        for expression in expressions {
            assert_no_temporary_names_in_expression(kernel, expression);
        }
    }
}

fn assert_no_temporary_names_in_expression(kernel: &Kernel, expression: ExprId) {
    match kernel.expr_node(expression).clone() {
        axeyum_lean_kernel::ExprNode::Const(name, _) => {
            assert!(!kernel.display_name(name).to_string().contains("_nested"));
        }
        axeyum_lean_kernel::ExprNode::Proj(type_name, _, structure) => {
            assert!(
                !kernel
                    .display_name(type_name)
                    .to_string()
                    .contains("_nested")
            );
            assert_no_temporary_names_in_expression(kernel, structure);
        }
        axeyum_lean_kernel::ExprNode::App(function, argument) => {
            assert_no_temporary_names_in_expression(kernel, function);
            assert_no_temporary_names_in_expression(kernel, argument);
        }
        axeyum_lean_kernel::ExprNode::Lam(_, ty, body, _)
        | axeyum_lean_kernel::ExprNode::Pi(_, ty, body, _) => {
            assert_no_temporary_names_in_expression(kernel, ty);
            assert_no_temporary_names_in_expression(kernel, body);
        }
        axeyum_lean_kernel::ExprNode::Let(_, ty, value, body) => {
            assert_no_temporary_names_in_expression(kernel, ty);
            assert_no_temporary_names_in_expression(kernel, value);
            assert_no_temporary_names_in_expression(kernel, body);
        }
        axeyum_lean_kernel::ExprNode::Sort(_)
        | axeyum_lean_kernel::ExprNode::BVar(_)
        | axeyum_lean_kernel::ExprNode::FVar(_)
        | axeyum_lean_kernel::ExprNode::Lit(_) => {}
    }
}

#[test]
fn one_family_nested_container_restores_exact_public_surface() {
    let mut kernel = Kernel::new();
    let root = kernel.anon();
    let (box_name, wrap) = declare_box(&mut kernel);
    let rose = kernel.name_str(root, "M2Rose");
    let node = kernel.name_str(rose, "node");
    let rose_rec = kernel.name_str(rose, "rec");
    let rose_aux_rec = kernel.name_str(rose, "rec_1");
    let field = kernel.name_str(root, "children");

    let type_ = sort_one(&mut kernel);
    let rose_const = kernel.const_(rose, vec![]);
    let box_const = kernel.const_(box_name, vec![]);
    let box_rose = kernel.app(box_const, rose_const);
    let node_type = kernel.pi(field, box_rose, rose_const, BinderInfo::Default);
    kernel
        .add_inductive(rose, &[], 0, type_, &[(node, node_type)])
        .expect("nested container expands, checks, restores, and publishes");

    assert!(kernel.environment().contains(rose));
    assert!(kernel.environment().contains(node));
    assert!(kernel.environment().contains(rose_rec));
    assert!(kernel.environment().contains(rose_aux_rec));
    assert_eq!(
        kernel.display_name(rose_aux_rec).to_string(),
        "M2Rose.rec_1"
    );

    let Declaration::Constructor { ty, .. } = kernel.environment().get(node).unwrap() else {
        panic!("restored node constructor");
    };
    assert_eq!(*ty, node_type);

    let Declaration::Recursor {
        rec_rules: main_rules,
        ..
    } = kernel.environment().get(rose_rec).unwrap()
    else {
        panic!("restored main recursor");
    };
    assert_eq!(main_rules.len(), 1);
    assert_eq!(main_rules[0].ctor_name, node);

    let Declaration::Recursor {
        rec_rules: auxiliary_rules,
        ..
    } = kernel.environment().get(rose_aux_rec).unwrap()
    else {
        panic!("restored auxiliary recursor");
    };
    assert_eq!(auxiliary_rules.len(), 1);
    assert_eq!(auxiliary_rules[0].ctor_name, wrap);

    let public_names = kernel
        .environment()
        .iter()
        .map(|(name, _)| kernel.display_name(*name).to_string())
        .collect::<Vec<_>>();
    assert!(public_names.iter().all(|name| !name.contains("_nested")));
    assert_eq!(kernel.environment().len(), 7);

    for (_, declaration) in kernel
        .environment()
        .iter()
        .map(|(name, declaration)| (*name, declaration.clone()))
        .collect::<Vec<_>>()
    {
        let inferred = kernel
            .infer(declaration.ty())
            .expect("every final public declaration type infers");
        assert!(matches!(
            kernel.expr_node(inferred),
            axeyum_lean_kernel::ExprNode::Sort(_)
        ));
        if let Declaration::Recursor { rec_rules, .. } = declaration {
            for rule in rec_rules {
                kernel
                    .infer(rule.value)
                    .expect("every final public recursor rule infers");
            }
        }
    }
}

#[test]
fn main_and_auxiliary_recursors_compute_across_the_restored_boundary() {
    let mut kernel = Kernel::new();
    let root = kernel.anon();
    let (box_name, wrap) = declare_box(&mut kernel);
    let (result_nat, result_zero, result_succ) = declare_nat_like(&mut kernel);
    let rose = kernel.name_str(root, "M2ComputationRose");
    let leaf = kernel.name_str(rose, "leaf");
    let node = kernel.name_str(rose, "node");
    let children = kernel.name_str(root, "children");
    let type_ = sort_one(&mut kernel);
    let rose_const = kernel.const_(rose, vec![]);
    let box_const = kernel.const_(box_name, vec![]);
    let box_rose = kernel.app(box_const, rose_const);
    let node_type = kernel.pi(children, box_rose, rose_const, BinderInfo::Default);
    kernel
        .add_inductive(
            rose,
            &[],
            0,
            type_,
            &[(leaf, rose_const), (node, node_type)],
        )
        .expect("computing nested family admits");

    let rose_rec = kernel.name_str(rose, "rec");
    let auxiliary_rec = kernel.name_str(rose, "rec_1");
    let result_const = kernel.const_(result_nat, vec![]);
    let motive_argument = kernel.name_str(root, "major");
    let rose_motive = kernel.lam(
        motive_argument,
        rose_const,
        result_const,
        BinderInfo::Default,
    );
    let box_motive = kernel.lam(motive_argument, box_rose, result_const, BinderInfo::Default);
    let zero_minor = kernel.const_(result_zero, vec![]);
    let succ_const = kernel.const_(result_succ, vec![]);
    let ih = kernel.name_str(root, "ih");
    let ih_value = kernel.bvar(0);
    let succ_ih = kernel.app(succ_const, ih_value);
    let node_ih = kernel.lam(ih, result_const, succ_ih, BinderInfo::Default);
    let node_minor = kernel.lam(children, box_rose, node_ih, BinderInfo::Default);
    let value = kernel.name_str(root, "value");
    let wrap_ih = kernel.lam(ih, result_const, succ_ih, BinderInfo::Default);
    let wrap_minor = kernel.lam(value, rose_const, wrap_ih, BinderInfo::Default);

    let leaf_value = kernel.const_(leaf, vec![]);
    let wrap_const = kernel.const_(wrap, vec![]);
    let boxed_leaf = kernel.app(wrap_const, rose_const);
    let boxed_leaf = kernel.app(boxed_leaf, leaf_value);
    let node_const = kernel.const_(node, vec![]);
    let rose_value = kernel.app(node_const, boxed_leaf);

    let recursor = kernel.environment().get(rose_rec).unwrap().clone();
    let recursor_levels = recursor
        .uparams()
        .iter()
        .map(|&parameter| kernel.level_param(parameter))
        .collect::<Vec<_>>();
    let mut application = kernel.const_(rose_rec, recursor_levels);
    for argument in [
        rose_motive,
        box_motive,
        zero_minor,
        node_minor,
        wrap_minor,
        rose_value,
    ] {
        application = kernel.app(application, argument);
    }

    let first_step = kernel.whnf(application);
    let (first_head, first_arguments) = unfold_apps(&kernel, first_step);
    assert_eq!(first_head, succ_const);
    assert_eq!(first_arguments.len(), 1);
    let (auxiliary_head, _) = unfold_apps(&kernel, first_arguments[0]);
    let auxiliary_uparams = kernel
        .environment()
        .get(auxiliary_rec)
        .unwrap()
        .uparams()
        .to_vec();
    let auxiliary_levels = auxiliary_uparams
        .into_iter()
        .map(|parameter| kernel.level_param(parameter))
        .collect();
    let expected_auxiliary = kernel.const_(auxiliary_rec, auxiliary_levels);
    assert_eq!(auxiliary_head, expected_auxiliary);

    let second_step = kernel.whnf(first_arguments[0]);
    let (second_head, second_arguments) = unfold_apps(&kernel, second_step);
    assert_eq!(second_head, succ_const);
    assert_eq!(second_arguments.len(), 1);
    let (main_head, _) = unfold_apps(&kernel, second_arguments[0]);
    let main_levels = recursor
        .uparams()
        .iter()
        .map(|&parameter| kernel.level_param(parameter))
        .collect();
    let expected_main = kernel.const_(rose_rec, main_levels);
    assert_eq!(main_head, expected_main);
    assert_eq!(kernel.whnf(second_arguments[0]), zero_minor);

    let once = kernel.app(succ_const, zero_minor);
    let twice = kernel.app(succ_const, once);
    assert!(kernel.def_eq(application, twice));
}

#[test]
fn repeated_nested_application_reuses_one_auxiliary_family() {
    let mut kernel = Kernel::new();
    let root = kernel.anon();
    let (box_name, _) = declare_box(&mut kernel);
    let rose = kernel.name_str(root, "M2RepeatRose");
    let node = kernel.name_str(rose, "node");
    let first = kernel.name_str(root, "first");
    let second = kernel.name_str(root, "second");
    let type_ = sort_one(&mut kernel);
    let rose_const = kernel.const_(rose, vec![]);
    let box_const = kernel.const_(box_name, vec![]);
    let box_rose = kernel.app(box_const, rose_const);
    let second_field = kernel.pi(second, box_rose, rose_const, BinderInfo::Default);
    let node_type = kernel.pi(first, box_rose, second_field, BinderInfo::Default);

    kernel
        .add_inductive(rose, &[], 0, type_, &[(node, node_type)])
        .expect("identical structural container applications reuse one auxiliary");

    let rec_1 = kernel.name_str(rose, "rec_1");
    let rec_2 = kernel.name_str(rose, "rec_2");
    assert!(kernel.environment().contains(rec_1));
    assert!(!kernel.environment().contains(rec_2));
    assert_no_temporary_names(&kernel);
}

#[test]
fn distinct_parameterizations_and_outer_mutual_cross_recursion_restore_in_order() {
    let mut kernel = Kernel::new();
    let root = kernel.anon();
    let (box_name, wrap) = declare_box(&mut kernel);
    let first = kernel.name_str(root, "M2MutualFirst");
    let second = kernel.name_str(root, "M2MutualSecond");
    let first_node = kernel.name_str(first, "node");
    let second_node = kernel.name_str(second, "node");
    let nested_field = kernel.name_str(root, "nested");
    let cross_field = kernel.name_str(root, "cross");
    let type_ = sort_one(&mut kernel);
    let box_const = kernel.const_(box_name, vec![]);
    let first_const = kernel.const_(first, vec![]);
    let second_const = kernel.const_(second, vec![]);
    let box_first = kernel.app(box_const, first_const);
    let box_second = kernel.app(box_const, second_const);
    let first_cross = kernel.pi(cross_field, second_const, first_const, BinderInfo::Default);
    let first_type = kernel.pi(nested_field, box_first, first_cross, BinderInfo::Default);
    let second_cross = kernel.pi(cross_field, first_const, second_const, BinderInfo::Default);
    let second_type = kernel.pi(nested_field, box_second, second_cross, BinderInfo::Default);
    let families = [
        InductiveFamilySpec::new(first, type_, vec![(first_node, first_type)]),
        InductiveFamilySpec::new(second, type_, vec![(second_node, second_type)]),
    ];

    kernel
        .add_mutual_inductive(&[], 0, &families)
        .expect("outer mutual self/cross/nested group admits");

    let first_rec = kernel.name_str(first, "rec");
    let second_rec = kernel.name_str(second, "rec");
    let rec_1 = kernel.name_str(first, "rec_1");
    let rec_2 = kernel.name_str(first, "rec_2");
    for name in [first_rec, second_rec, rec_1, rec_2] {
        assert!(kernel.environment().contains(name));
    }
    for auxiliary in [rec_1, rec_2] {
        let Declaration::Recursor { rec_rules, .. } = kernel.environment().get(auxiliary).unwrap()
        else {
            panic!("restored auxiliary recursor");
        };
        assert_eq!(rec_rules.len(), 1);
        assert_eq!(rec_rules[0].ctor_name, wrap);
    }
    assert_no_temporary_names(&kernel);
}

#[test]
fn outer_parameter_is_rebound_without_free_variable_leakage() {
    let mut kernel = Kernel::new();
    let root = kernel.anon();
    let (box_name, _) = declare_box(&mut kernel);
    let tree = kernel.name_str(root, "M2ParameterizedTree");
    let node = kernel.name_str(tree, "node");
    let alpha = kernel.name_str(root, "alpha");
    let children = kernel.name_str(root, "children");
    let type_ = sort_one(&mut kernel);
    let family_type = kernel.pi(alpha, type_, type_, BinderInfo::Implicit);

    let tree_const = kernel.const_(tree, vec![]);
    let box_const = kernel.const_(box_name, vec![]);
    let alpha_argument = kernel.bvar(0);
    let tree_alpha = kernel.app(tree_const, alpha_argument);
    let box_tree_alpha = kernel.app(box_const, tree_alpha);
    let result_alpha = kernel.bvar(1);
    let result = kernel.app(tree_const, result_alpha);
    let child_field = kernel.pi(children, box_tree_alpha, result, BinderInfo::Default);
    let node_type = kernel.pi(alpha, type_, child_field, BinderInfo::Implicit);

    kernel
        .add_inductive(tree, &[], 1, family_type, &[(node, node_type)])
        .expect("outer parameter is canonicalized and restored");
    let Declaration::Constructor { ty, .. } = kernel.environment().get(node).unwrap() else {
        panic!("restored parameterized constructor");
    };
    assert_eq!(*ty, node_type);
    assert_no_temporary_names(&kernel);
}

#[test]
fn two_outer_parameters_can_specialize_a_one_parameter_container() {
    let mut kernel = Kernel::new();
    let root = kernel.anon();
    let (box_name, _) = declare_box(&mut kernel);
    let family = kernel.name_str(root, "M2TwoParameterTree");
    let node = kernel.name_str(family, "node");
    let alpha = kernel.name_str(root, "alpha");
    let beta = kernel.name_str(root, "beta");
    let children = kernel.name_str(root, "children");
    let type_ = sort_one(&mut kernel);
    let beta_type = kernel.pi(beta, type_, type_, BinderInfo::Implicit);
    let family_type = kernel.pi(alpha, type_, beta_type, BinderInfo::Implicit);
    let family_const = kernel.const_(family, vec![]);
    let alpha_argument = kernel.bvar(1);
    let beta_argument = kernel.bvar(0);
    let family_at_parameters = kernel.app(family_const, alpha_argument);
    let family_at_parameters = kernel.app(family_at_parameters, beta_argument);
    let box_const = kernel.const_(box_name, vec![]);
    let nested = kernel.app(box_const, family_at_parameters);
    let result_alpha = kernel.bvar(2);
    let result_beta = kernel.bvar(1);
    let result = kernel.app(family_const, result_alpha);
    let result = kernel.app(result, result_beta);
    let fields = kernel.pi(children, nested, result, BinderInfo::Default);
    let beta_fields = kernel.pi(beta, type_, fields, BinderInfo::Implicit);
    let constructor_type = kernel.pi(alpha, type_, beta_fields, BinderInfo::Implicit);

    kernel
        .add_inductive(family, &[], 2, family_type, &[(node, constructor_type)])
        .expect("outer and container parameter counts may differ");
    let Declaration::Constructor { ty, .. } = kernel.environment().get(node).unwrap() else {
        panic!("restored two-parameter constructor");
    };
    assert_eq!(*ty, constructor_type);
    assert_no_temporary_names(&kernel);
}

#[test]
fn indexed_container_retains_indices_while_specializing_parameters() {
    let mut kernel = Kernel::new();
    let root = kernel.anon();
    let (index, zero) = declare_index_type(&mut kernel);
    let (indexed_box, indexed_wrap) = declare_indexed_box(&mut kernel, index);
    let rose = kernel.name_str(root, "M2IndexedRose");
    let node = kernel.name_str(rose, "node");
    let children = kernel.name_str(root, "children");
    let type_ = sort_one(&mut kernel);
    let rose_const = kernel.const_(rose, vec![]);
    let container = kernel.const_(indexed_box, vec![]);
    let indexed = kernel.app(container, rose_const);
    let zero_value = kernel.const_(zero, vec![]);
    let indexed = kernel.app(indexed, zero_value);
    let node_type = kernel.pi(children, indexed, rose_const, BinderInfo::Default);

    kernel
        .add_inductive(rose, &[], 0, type_, &[(node, node_type)])
        .expect("container parameter specializes while its index remains applied");

    let rec_1 = kernel.name_str(rose, "rec_1");
    let Declaration::Recursor {
        num_indices,
        rec_rules,
        ..
    } = kernel.environment().get(rec_1).unwrap()
    else {
        panic!("restored indexed auxiliary recursor");
    };
    assert_eq!(*num_indices, 1);
    assert_eq!(rec_rules[0].ctor_name, indexed_wrap);
    assert_no_temporary_names(&kernel);
}

#[test]
fn two_container_indices_survive_expansion_and_restoration() {
    let mut kernel = Kernel::new();
    let root = kernel.anon();
    let (index, zero) = declare_index_type(&mut kernel);
    let (container, constructor) = declare_double_indexed_box(&mut kernel, index);
    let rose = kernel.name_str(root, "M2DoubleIndexedRose");
    let node = kernel.name_str(rose, "node");
    let children = kernel.name_str(root, "children");
    let type_ = sort_one(&mut kernel);
    let rose_const = kernel.const_(rose, vec![]);
    let container_const = kernel.const_(container, vec![]);
    let zero_value = kernel.const_(zero, vec![]);
    let nested = kernel.app(container_const, rose_const);
    let nested = kernel.app(nested, zero_value);
    let nested = kernel.app(nested, zero_value);
    let node_type = kernel.pi(children, nested, rose_const, BinderInfo::Default);

    kernel
        .add_inductive(rose, &[], 0, type_, &[(node, node_type)])
        .expect("both container indices remain trailing auxiliary arguments");
    let rec_1 = kernel.name_str(rose, "rec_1");
    let Declaration::Recursor {
        num_indices,
        rec_rules,
        ..
    } = kernel.environment().get(rec_1).unwrap()
    else {
        panic!("restored two-index auxiliary recursor");
    };
    assert_eq!(*num_indices, 2);
    assert_eq!(rec_rules[0].ctor_name, constructor);
    assert_no_temporary_names(&kernel);
}

#[test]
fn container_universes_are_instantiated_into_outer_universes() {
    let mut kernel = Kernel::new();
    let root = kernel.anon();
    let (box_name, wrap, _) = declare_polymorphic_box(&mut kernel);
    let outer_universe = kernel.name_str(root, "outerUniverse");
    let level = kernel.level_param(outer_universe);
    let sort = kernel.sort(level);
    let rose = kernel.name_str(root, "M2UniverseRose");
    let node = kernel.name_str(rose, "node");
    let children = kernel.name_str(root, "children");
    let rose_const = kernel.const_(rose, vec![level]);
    let box_const = kernel.const_(box_name, vec![level]);
    let box_rose = kernel.app(box_const, rose_const);
    let node_type = kernel.pi(children, box_rose, rose_const, BinderInfo::Default);

    kernel
        .add_inductive(rose, &[outer_universe], 0, sort, &[(node, node_type)])
        .expect("container universe parameters specialize to the outer declaration levels");
    let rec_1 = kernel.name_str(rose, "rec_1");
    let Declaration::Recursor { rec_rules, .. } = kernel.environment().get(rec_1).unwrap() else {
        panic!("restored universe-polymorphic auxiliary recursor");
    };
    assert_eq!(rec_rules[0].ctor_name, wrap);
    assert_no_temporary_names(&kernel);
}

#[test]
fn complete_existing_mutual_container_group_is_copied_and_restored() {
    let mut kernel = Kernel::new();
    let root = kernel.anon();
    let (left, _, left_make, right_make) = declare_mutual_container(&mut kernel);
    let rose = kernel.name_str(root, "M2MutualContainerRose");
    let node = kernel.name_str(rose, "node");
    let children = kernel.name_str(root, "children");
    let type_ = sort_one(&mut kernel);
    let rose_const = kernel.const_(rose, vec![]);
    let left_const = kernel.const_(left, vec![]);
    let left_rose = kernel.app(left_const, rose_const);
    let node_type = kernel.pi(children, left_rose, rose_const, BinderInfo::Default);

    kernel
        .add_inductive(rose, &[], 0, type_, &[(node, node_type)])
        .expect("selecting one mutual container copies its complete checked group");

    let rec_1 = kernel.name_str(rose, "rec_1");
    let rec_2 = kernel.name_str(rose, "rec_2");
    for (recursor, constructor) in [(rec_1, left_make), (rec_2, right_make)] {
        let Declaration::Recursor { rec_rules, .. } = kernel.environment().get(recursor).unwrap()
        else {
            panic!("restored mutual-container auxiliary recursor");
        };
        assert_eq!(rec_rules.len(), 1);
        assert_eq!(rec_rules[0].ctor_name, constructor);
    }
    assert_no_temporary_names(&kernel);
}

#[test]
fn copied_empty_container_owner_gets_an_empty_public_auxiliary_recursor() {
    let mut kernel = Kernel::new();
    let root = kernel.anon();
    let (occupied, _, make) = declare_container_group_with_empty_owner(&mut kernel);
    let rose = kernel.name_str(root, "M2EmptyOwnerRose");
    let node = kernel.name_str(rose, "node");
    let children = kernel.name_str(root, "children");
    let type_ = sort_one(&mut kernel);
    let rose_const = kernel.const_(rose, vec![]);
    let occupied_const = kernel.const_(occupied, vec![]);
    let occupied_rose = kernel.app(occupied_const, rose_const);
    let node_type = kernel.pi(children, occupied_rose, rose_const, BinderInfo::Default);

    kernel
        .add_inductive(rose, &[], 0, type_, &[(node, node_type)])
        .expect("complete container copying retains its empty owner");
    let rec_1 = kernel.name_str(rose, "rec_1");
    let rec_2 = kernel.name_str(rose, "rec_2");
    let Declaration::Recursor {
        rec_rules: occupied_rules,
        ..
    } = kernel.environment().get(rec_1).unwrap()
    else {
        panic!("occupied auxiliary recursor");
    };
    assert_eq!(occupied_rules.len(), 1);
    assert_eq!(occupied_rules[0].ctor_name, make);
    let Declaration::Recursor {
        rec_rules: empty_rules,
        ..
    } = kernel.environment().get(rec_2).unwrap()
    else {
        panic!("empty auxiliary recursor");
    };
    assert!(empty_rules.is_empty());
    assert_no_temporary_names(&kernel);
}

#[test]
fn fixed_point_expansion_and_restoration_cover_two_container_levels() {
    let mut kernel = Kernel::new();
    let root = kernel.anon();
    let (box_name, box_wrap) = declare_box(&mut kernel);
    let (outer_box, outer_make) = declare_container_over_box(&mut kernel, box_name);
    let rose = kernel.name_str(root, "M2DepthTwoRose");
    let node = kernel.name_str(rose, "node");
    let children = kernel.name_str(root, "children");
    let type_ = sort_one(&mut kernel);
    let rose_const = kernel.const_(rose, vec![]);
    let outer_const = kernel.const_(outer_box, vec![]);
    let outer_rose = kernel.app(outer_const, rose_const);
    let node_type = kernel.pi(children, outer_rose, rose_const, BinderInfo::Default);

    kernel
        .add_inductive(rose, &[], 0, type_, &[(node, node_type)])
        .expect("copied container constructors queue nested containers to fixed point");

    let rec_1 = kernel.name_str(rose, "rec_1");
    let rec_2 = kernel.name_str(rose, "rec_2");
    for (recursor, constructor) in [(rec_1, outer_make), (rec_2, box_wrap)] {
        let Declaration::Recursor { rec_rules, .. } = kernel.environment().get(recursor).unwrap()
        else {
            panic!("restored depth-two auxiliary recursor");
        };
        assert_eq!(rec_rules[0].ctor_name, constructor);
    }
    assert_no_temporary_names(&kernel);
}

#[test]
fn restored_parameterized_family_is_a_complete_later_container() {
    let mut kernel = Kernel::new();
    let root = kernel.anon();
    let (box_name, box_wrap) = declare_box(&mut kernel);
    let tree = kernel.name_str(root, "M2RestoredTree");
    let tree_node = kernel.name_str(tree, "node");
    let alpha = kernel.name_str(root, "alpha");
    let children = kernel.name_str(root, "children");
    let type_ = sort_one(&mut kernel);
    let tree_type = kernel.pi(alpha, type_, type_, BinderInfo::Implicit);
    let tree_const = kernel.const_(tree, vec![]);
    let box_const = kernel.const_(box_name, vec![]);
    let alpha_argument = kernel.bvar(0);
    let tree_alpha = kernel.app(tree_const, alpha_argument);
    let box_tree_alpha = kernel.app(box_const, tree_alpha);
    let result_argument = kernel.bvar(1);
    let tree_result = kernel.app(tree_const, result_argument);
    let tree_fields = kernel.pi(children, box_tree_alpha, tree_result, BinderInfo::Default);
    let tree_constructor = kernel.pi(alpha, type_, tree_fields, BinderInfo::Implicit);
    kernel
        .add_inductive(tree, &[], 1, tree_type, &[(tree_node, tree_constructor)])
        .expect("first nested parameterized family restores");

    let grove = kernel.name_str(root, "M2Grove");
    let branch = kernel.name_str(grove, "branch");
    let grove_const = kernel.const_(grove, vec![]);
    let tree_grove = kernel.app(tree_const, grove_const);
    let branch_type = kernel.pi(children, tree_grove, grove_const, BinderInfo::Default);
    kernel
        .add_inductive(grove, &[], 0, type_, &[(branch, branch_type)])
        .expect("restored source-only group metadata supports a later nested copy");

    let rec_1 = kernel.name_str(grove, "rec_1");
    let rec_2 = kernel.name_str(grove, "rec_2");
    for (recursor, constructor) in [(rec_1, tree_node), (rec_2, box_wrap)] {
        let Declaration::Recursor { rec_rules, .. } = kernel.environment().get(recursor).unwrap()
        else {
            panic!("later restored auxiliary recursor");
        };
        assert_eq!(rec_rules[0].ctor_name, constructor);
    }
    assert_no_temporary_names(&kernel);
}

#[test]
fn higher_order_field_tail_discovers_nested_container() {
    let mut kernel = Kernel::new();
    let root = kernel.anon();
    let (box_name, _) = declare_box(&mut kernel);
    let (index, _) = declare_index_type(&mut kernel);
    let rose = kernel.name_str(root, "M2HigherOrderRose");
    let node = kernel.name_str(rose, "node");
    let function = kernel.name_str(root, "function");
    let argument = kernel.name_str(root, "argument");
    let type_ = sort_one(&mut kernel);
    let rose_const = kernel.const_(rose, vec![]);
    let box_const = kernel.const_(box_name, vec![]);
    let box_rose = kernel.app(box_const, rose_const);
    let index_const = kernel.const_(index, vec![]);
    let function_type = kernel.pi(argument, index_const, box_rose, BinderInfo::Default);
    let node_type = kernel.pi(function, function_type, rose_const, BinderInfo::Default);

    kernel
        .add_inductive(rose, &[], 0, type_, &[(node, node_type)])
        .expect("nested application at a positive higher-order tail admits");
    let rec_1 = kernel.name_str(rose, "rec_1");
    assert!(kernel.environment().contains(rec_1));
    assert_no_temporary_names(&kernel);
}

#[test]
fn allowed_prop_result_restores_nested_auxiliary_recursor() {
    let mut kernel = Kernel::new();
    let root = kernel.anon();
    let (box_name, _) = declare_prop_box(&mut kernel);
    let rose = kernel.name_str(root, "M2PropRose");
    let node = kernel.name_str(rose, "node");
    let children = kernel.name_str(root, "children");
    let prop = kernel.sort_zero();
    let rose_const = kernel.const_(rose, vec![]);
    let box_const = kernel.const_(box_name, vec![]);
    let box_rose = kernel.app(box_const, rose_const);
    let node_type = kernel.pi(children, box_rose, rose_const, BinderInfo::Default);

    kernel
        .add_inductive(rose, &[], 0, prop, &[(node, node_type)])
        .expect("allowed Prop nested family admits through the same restoration path");
    let rec_1 = kernel.name_str(rose, "rec_1");
    assert!(kernel.environment().contains(rec_1));
    assert_no_temporary_names(&kernel);
}

#[test]
fn incomplete_container_parameter_prefix_is_typed_and_transactional() {
    let mut kernel = Kernel::new();
    let root = kernel.anon();
    let container = declare_two_parameter_container(&mut kernel);
    let rose = kernel.name_str(root, "M2IncompleteRose");
    let node = kernel.name_str(rose, "node");
    let field = kernel.name_str(root, "field");
    let type_ = sort_one(&mut kernel);
    let rose_const = kernel.const_(rose, vec![]);
    let container_const = kernel.const_(container, vec![]);
    let incomplete = kernel.app(container_const, rose_const);
    let node_type = kernel.pi(field, incomplete, rose_const, BinderInfo::Default);
    let before = declarations(&kernel);

    assert_eq!(
        kernel.add_inductive(rose, &[], 0, type_, &[(node, node_type)]),
        Err(KernelError::NestedInductiveIncompleteApplication { container })
    );
    assert_eq!(declarations(&kernel), before);
}

#[test]
fn loose_nested_parameter_is_typed_and_transactional() {
    let mut kernel = Kernel::new();
    let root = kernel.anon();
    let (box_name, _) = declare_box(&mut kernel);
    let rose = kernel.name_str(root, "M2LooseRose");
    let node = kernel.name_str(rose, "node");
    let local = kernel.name_str(root, "local");
    let nested_binder = kernel.name_str(root, "nestedBinder");
    let field = kernel.name_str(root, "field");
    let type_ = sort_one(&mut kernel);
    let rose_const = kernel.const_(rose, vec![]);
    // Inside `local`, BVar(0) names that local. Wrapping it in one more Pi
    // makes BVar(1) the escaping local in the container parameter.
    let escaping_local = kernel.bvar(1);
    let parameter = kernel.pi(
        nested_binder,
        rose_const,
        escaping_local,
        BinderInfo::Default,
    );
    let box_const = kernel.const_(box_name, vec![]);
    let nested = kernel.app(box_const, parameter);
    let field_type = kernel.pi(field, nested, rose_const, BinderInfo::Default);
    let node_type = kernel.pi(local, type_, field_type, BinderInfo::Default);
    let before = declarations(&kernel);

    assert_eq!(
        kernel.add_inductive(rose, &[], 0, type_, &[(node, node_type)]),
        Err(KernelError::NestedInductiveLooseParameter {
            container: box_name,
        })
    );
    assert_eq!(declarations(&kernel), before);
}

#[test]
fn negative_occurrence_in_specialized_parameter_rejects_and_preserves_group_index() {
    let mut kernel = Kernel::new();
    let root = kernel.anon();
    let (box_name, _) = declare_box(&mut kernel);
    let (index, _) = declare_index_type(&mut kernel);
    let rose = kernel.name_str(root, "M2NegativeRose");
    let node = kernel.name_str(rose, "node");
    let argument = kernel.name_str(root, "argument");
    let field = kernel.name_str(root, "field");
    let type_ = sort_one(&mut kernel);
    let rose_const = kernel.const_(rose, vec![]);
    let index_const = kernel.const_(index, vec![]);
    let negative_parameter = kernel.pi(argument, rose_const, index_const, BinderInfo::Default);
    let box_const = kernel.const_(box_name, vec![]);
    let nested = kernel.app(box_const, negative_parameter);
    let node_type = kernel.pi(field, nested, rose_const, BinderInfo::Default);
    let before = declarations(&kernel);

    assert!(matches!(
        kernel.add_inductive(rose, &[], 0, type_, &[(node, node_type)]),
        Err(KernelError::NonPositiveInductiveOccurrence { .. })
    ));
    assert_eq!(declarations(&kernel), before);

    let retry = kernel.name_str(root, "M2NegativeRetryRose");
    let retry_node = kernel.name_str(retry, "node");
    let retry_const = kernel.const_(retry, vec![]);
    let retry_nested = kernel.app(box_const, retry_const);
    let retry_type = kernel.pi(field, retry_nested, retry_const, BinderInfo::Default);
    kernel
        .add_inductive(retry, &[], 0, type_, &[(retry_node, retry_type)])
        .expect("failed expansion preserves the pre-existing container group index");
}

#[test]
fn non_inductive_foreign_head_remains_a_typed_nested_rejection() {
    let mut kernel = Kernel::new();
    let root = kernel.anon();
    let foreign = kernel.name_str(root, "M2Foreign");
    let alpha = kernel.name_str(root, "alpha");
    let type_ = sort_one(&mut kernel);
    let foreign_type = kernel.pi(alpha, type_, type_, BinderInfo::Implicit);
    kernel
        .add_declaration(Declaration::Axiom {
            name: foreign,
            uparams: vec![],
            ty: foreign_type,
        })
        .expect("foreign type constructor axiom admits");
    let rose = kernel.name_str(root, "M2ForeignRose");
    let node = kernel.name_str(rose, "node");
    let field = kernel.name_str(root, "field");
    let rose_const = kernel.const_(rose, vec![]);
    let foreign_const = kernel.const_(foreign, vec![]);
    let foreign_rose = kernel.app(foreign_const, rose_const);
    let node_type = kernel.pi(field, foreign_rose, rose_const, BinderInfo::Default);
    let before = declarations(&kernel);

    assert!(matches!(
        kernel.add_inductive(rose, &[], 0, type_, &[(node, node_type)]),
        Err(KernelError::InvalidInductiveOccurrence { .. })
    ));
    assert_eq!(declarations(&kernel), before);
}

#[test]
fn public_auxiliary_recursor_collision_rolls_back_late_staging() {
    let mut kernel = Kernel::new();
    let root = kernel.anon();
    let (box_name, _) = declare_box(&mut kernel);
    let rose = kernel.name_str(root, "M2CollisionRose");
    let node = kernel.name_str(rose, "node");
    let rec_1 = kernel.name_str(rose, "rec_1");
    let prop = kernel.sort_zero();
    kernel
        .add_declaration(Declaration::Axiom {
            name: rec_1,
            uparams: vec![],
            ty: prop,
        })
        .expect("pre-existing public auxiliary name admits");
    let type_ = sort_one(&mut kernel);
    let rose_const = kernel.const_(rose, vec![]);
    let box_const = kernel.const_(box_name, vec![]);
    let box_rose = kernel.app(box_const, rose_const);
    let field = kernel.name_str(root, "field");
    let node_type = kernel.pi(field, box_rose, rose_const, BinderInfo::Default);
    let before = declarations(&kernel);

    assert_eq!(
        kernel.add_inductive(rose, &[], 0, type_, &[(node, node_type)]),
        Err(KernelError::DeclarationExists { name: rec_1 })
    );
    assert_eq!(declarations(&kernel), before);

    let retry = kernel.name_str(root, "M2CollisionRetryRose");
    let retry_node = kernel.name_str(retry, "node");
    let retry_const = kernel.const_(retry, vec![]);
    let retry_nested = kernel.app(box_const, retry_const);
    let retry_type = kernel.pi(field, retry_nested, retry_const, BinderInfo::Default);
    kernel
        .add_inductive(retry, &[], 0, type_, &[(retry_node, retry_type)])
        .expect("late rollback clears temporary declarations, metadata, and caches");
}

#[test]
fn temporary_name_generation_skips_source_surface_collisions() {
    let mut kernel = Kernel::new();
    let root = kernel.anon();
    let (box_name, _) = declare_box(&mut kernel);
    let rose = kernel.name_str(root, "M2FreshRose");
    let nested_namespace = kernel.name_str(rose, "_nested");
    let adversarial_constructor = kernel.name_num(nested_namespace, 1);
    let type_ = sort_one(&mut kernel);
    let rose_const = kernel.const_(rose, vec![]);
    let box_const = kernel.const_(box_name, vec![]);
    let box_rose = kernel.app(box_const, rose_const);
    let field = kernel.name_str(root, "field");
    let constructor_type = kernel.pi(field, box_rose, rose_const, BinderInfo::Default);

    kernel
        .add_inductive(
            rose,
            &[],
            0,
            type_,
            &[(adversarial_constructor, constructor_type)],
        )
        .expect("private freshness skips a source constructor collision");
    assert!(kernel.environment().contains(adversarial_constructor));
    let rec_1 = kernel.name_str(rose, "rec_1");
    assert!(kernel.environment().contains(rec_1));
}

#[test]
fn noncanonical_inductive_without_group_metadata_rejects_copying() {
    let mut kernel = Kernel::new();
    let root = kernel.anon();
    let fake = kernel.name_str(root, "M2UnindexedContainer");
    let alpha = kernel.name_str(root, "alpha");
    let type_ = sort_one(&mut kernel);
    let fake_type = kernel.pi(alpha, type_, type_, BinderInfo::Implicit);
    kernel
        .add_declaration(Declaration::Inductive {
            name: fake,
            uparams: vec![],
            ty: fake_type,
            num_params: 1,
            num_indices: 0,
            is_recursive: false,
            ctor_names: vec![],
        })
        .expect("legacy generic declaration gate can stage noncanonical metadata");
    let rose = kernel.name_str(root, "M2MalformedContainerRose");
    let node = kernel.name_str(rose, "node");
    let field = kernel.name_str(root, "field");
    let rose_const = kernel.const_(rose, vec![]);
    let fake_const = kernel.const_(fake, vec![]);
    let fake_rose = kernel.app(fake_const, rose_const);
    let node_type = kernel.pi(field, fake_rose, rose_const, BinderInfo::Default);
    let before = declarations(&kernel);

    assert_eq!(
        kernel.add_inductive(rose, &[], 0, type_, &[(node, node_type)]),
        Err(KernelError::NestedInductiveMalformedContainer { container: fake })
    );
    assert_eq!(declarations(&kernel), before);
}

#[test]
fn expansion_limit_is_typed_before_environment_mutation() {
    let mut kernel = Kernel::new();
    let root = kernel.anon();
    let (box_name, _) = declare_box(&mut kernel);
    let rose = kernel.name_str(root, "M2LimitRose");
    let node = kernel.name_str(rose, "node");
    let rose_const = kernel.const_(rose, vec![]);
    let box_const = kernel.const_(box_name, vec![]);
    let mut constructor_type = rose_const;
    let parameter_binder = kernel.name_str(root, "parameter");
    for index in (0..=256_u64).rev() {
        let mut parameter = rose_const;
        for _ in 0..=index {
            parameter = kernel.pi(parameter_binder, rose_const, parameter, BinderInfo::Default);
        }
        let nested = kernel.app(box_const, parameter);
        let field = kernel.name_num(node, index);
        constructor_type = kernel.pi(field, nested, constructor_type, BinderInfo::Default);
    }
    let type_ = sort_one(&mut kernel);
    let before = declarations(&kernel);

    assert_eq!(
        kernel.add_inductive(rose, &[], 0, type_, &[(node, constructor_type)]),
        Err(KernelError::NestedInductiveExpansionLimit { limit: 256 })
    );
    assert_eq!(declarations(&kernel), before);
}
