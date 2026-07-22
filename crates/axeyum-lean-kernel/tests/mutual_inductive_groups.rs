//! TL2.13 M2 native mutual-inductive semantics and transaction gates.
//!
//! These tests cover the preregistered singleton, cross-family, indexed,
//! higher-order, mixed, empty-family, mutual-`Prop`, typed-negative, and late-
//! rollback shapes without widening the importer or observing M0 streams.

use axeyum_lean_kernel::{
    BinderInfo, Declaration, ExprId, InductiveFamilySpec, Kernel, KernelError, NameId,
};

fn sort_one(kernel: &mut Kernel) -> ExprId {
    let zero = kernel.level_zero();
    let one = kernel.level_succ(zero);
    kernel.sort(one)
}

fn sort_two(kernel: &mut Kernel) -> ExprId {
    let zero = kernel.level_zero();
    let one = kernel.level_succ(zero);
    let two = kernel.level_succ(one);
    kernel.sort(two)
}

fn declarations(kernel: &Kernel) -> Vec<Declaration> {
    kernel
        .environment()
        .iter()
        .map(|(_, declaration)| declaration.clone())
        .collect()
}

fn empty_family(name: NameId, ty: ExprId) -> InductiveFamilySpec {
    InductiveFamilySpec::new(name, ty, Vec::new())
}

fn pi_arity(kernel: &Kernel, mut expression: ExprId) -> usize {
    let mut arity = 0;
    while let axeyum_lean_kernel::ExprNode::Pi(_, _, body, _) = kernel.expr_node(expression).clone()
    {
        arity += 1;
        expression = body;
    }
    arity
}

fn assert_group_contract(
    kernel: &mut Kernel,
    families: &[InductiveFamilySpec],
    num_params: usize,
    num_indices: &[usize],
    is_recursive: bool,
) {
    assert_eq!(families.len(), num_indices.len());
    let total_minors: usize = families
        .iter()
        .map(|family| family.constructors.len())
        .sum();
    for (family, &expected_indices) in families.iter().zip(num_indices) {
        let family_declaration = kernel
            .environment()
            .get(family.name)
            .expect("family declaration")
            .clone();
        let Declaration::Inductive {
            num_params: actual_params,
            num_indices: actual_indices,
            is_recursive: actual_recursive,
            ctor_names,
            ..
        } = family_declaration
        else {
            panic!("expected inductive declaration");
        };
        assert_eq!(usize::from(actual_params), num_params);
        assert_eq!(usize::from(actual_indices), expected_indices);
        assert_eq!(actual_recursive, is_recursive);
        assert_eq!(
            ctor_names,
            family
                .constructors
                .iter()
                .map(|(name, _)| *name)
                .collect::<Vec<_>>()
        );
        for (constructor_index, &(constructor, ty)) in family.constructors.iter().enumerate() {
            let Declaration::Constructor {
                inductive,
                idx,
                num_fields,
                ..
            } = kernel.environment().get(constructor).unwrap()
            else {
                panic!("expected constructor declaration");
            };
            assert_eq!(*inductive, family.name);
            assert_eq!(usize::from(*idx), constructor_index);
            assert_eq!(usize::from(*num_fields), pi_arity(kernel, ty) - num_params);
        }

        let recursor = kernel.name_str(family.name, "rec");
        let declaration = kernel.environment().get(recursor).unwrap().clone();
        let Declaration::Recursor {
            rec_rules,
            num_motives,
            num_minors,
            num_params: actual_params,
            num_indices: actual_indices,
            ..
        } = &declaration
        else {
            panic!("expected recursor declaration");
        };
        assert_eq!(usize::from(*num_motives), families.len());
        assert_eq!(usize::from(*num_minors), total_minors);
        assert_eq!(usize::from(*actual_params), num_params);
        assert_eq!(usize::from(*actual_indices), expected_indices);
        assert_eq!(
            rec_rules
                .iter()
                .map(|rule| rule.ctor_name)
                .collect::<Vec<_>>(),
            family
                .constructors
                .iter()
                .map(|(name, _)| *name)
                .collect::<Vec<_>>()
        );
        for (rule, &(_, constructor_ty)) in rec_rules.iter().zip(&family.constructors) {
            assert_eq!(
                usize::from(rule.num_fields),
                pi_arity(kernel, constructor_ty) - num_params
            );
        }
        let inferred = kernel.infer(declaration.ty()).unwrap();
        assert!(matches!(
            kernel.expr_node(inferred),
            axeyum_lean_kernel::ExprNode::Sort(_)
        ));
    }
}

fn declare_nat_like(
    kernel: &mut Kernel,
    through_singleton_wrapper: bool,
) -> (NameId, NameId, NameId, NameId) {
    let root = kernel.anon();
    let nat = kernel.name_str(root, "M1Nat");
    let zero = kernel.name_str(nat, "zero");
    let succ = kernel.name_str(nat, "succ");
    let recursor = kernel.name_str(nat, "rec");
    let ty = sort_one(kernel);
    let nat_const = kernel.const_(nat, vec![]);
    let succ_ty = kernel.pi(root, nat_const, nat_const, BinderInfo::Default);
    let constructors = vec![(zero, nat_const), (succ, succ_ty)];

    if through_singleton_wrapper {
        kernel
            .add_inductive(nat, &[], 0, ty, &constructors)
            .expect("singleton wrapper admits the existing direct-recursive family");
    } else {
        kernel
            .add_mutual_inductive(&[], 0, &[InductiveFamilySpec::new(nat, ty, constructors)])
            .expect("one-family group path admits the existing direct-recursive family");
    }
    (nat, zero, succ, recursor)
}

fn assert_zero_iota(kernel: &mut Kernel, zero: NameId, recursor: NameId) {
    let declaration = kernel
        .environment()
        .get(recursor)
        .expect("generated recursor")
        .clone();
    let levels = declaration
        .uparams()
        .iter()
        .map(|&parameter| kernel.level_param(parameter))
        .collect();
    let motive = kernel.fvar(10);
    let zero_minor = kernel.fvar(11);
    let succ_minor = kernel.fvar(12);
    let zero_value = kernel.const_(zero, vec![]);
    let mut application = kernel.const_(recursor, levels);
    for argument in [motive, zero_minor, succ_minor, zero_value] {
        application = kernel.app(application, argument);
    }
    assert_eq!(kernel.whnf(application), zero_minor);
}

#[test]
fn singleton_wrapper_and_direct_group_path_are_exactly_equal_and_compute() {
    let mut wrapper = Kernel::new();
    let (_, wrapper_zero, _, wrapper_recursor) = declare_nat_like(&mut wrapper, true);
    let wrapper_declarations = declarations(&wrapper);
    assert_zero_iota(&mut wrapper, wrapper_zero, wrapper_recursor);

    let mut group = Kernel::new();
    let (_, group_zero, _, group_recursor) = declare_nat_like(&mut group, false);
    let group_declarations = declarations(&group);
    assert_zero_iota(&mut group, group_zero, group_recursor);

    assert_eq!(wrapper_declarations, group_declarations);
    assert_eq!(wrapper_zero, group_zero);
    assert_eq!(wrapper_recursor, group_recursor);
}

#[test]
fn empty_group_is_typed_and_preserves_the_environment() {
    let mut kernel = Kernel::new();
    let root = kernel.anon();
    let seed = kernel.name_str(root, "seed");
    let prop = kernel.sort_zero();
    kernel
        .add_declaration(Declaration::Axiom {
            name: seed,
            uparams: Vec::new(),
            ty: prop,
        })
        .expect("seed axiom admits");
    let before = declarations(&kernel);

    assert_eq!(
        kernel.add_mutual_inductive(&[], 0, &[]),
        Err(KernelError::EmptyInductiveGroup)
    );
    assert_eq!(declarations(&kernel), before);
}

#[test]
fn dependent_shared_parameters_and_per_family_indices_admit() {
    let mut kernel = Kernel::new();
    let root = kernel.anon();
    let alpha = kernel.name_str(root, "alpha");
    let value = kernel.name_str(root, "value");
    let index = kernel.name_str(root, "index");
    let even = kernel.name_str(root, "EvenDependent");
    let odd = kernel.name_str(root, "OddDependent");
    let result = sort_one(&mut kernel);
    let alpha_type = sort_one(&mut kernel);

    let alpha_bvar = kernel.bvar(0);
    let even_value = kernel.pi(value, alpha_bvar, result, BinderInfo::Default);
    let even_ty = kernel.pi(alpha, alpha_type, even_value, BinderInfo::Implicit);

    let indexed_alpha = kernel.bvar(1);
    let odd_indexed_result = kernel.pi(index, indexed_alpha, result, BinderInfo::Default);
    let odd_value = kernel.pi(value, alpha_bvar, odd_indexed_result, BinderInfo::Default);
    // Lean compares shared parameter types definitionally; binder annotations
    // do not change the common parameter telescope.
    let odd_ty = kernel.pi(alpha, alpha_type, odd_value, BinderInfo::StrictImplicit);
    let families = [empty_family(even, even_ty), empty_family(odd, odd_ty)];
    kernel
        .add_mutual_inductive(&[], 2, &families)
        .expect("definitionally equal dependent parameters admit");
    assert_group_contract(&mut kernel, &families, 2, &[0, 1], false);
    for (family, num_indices) in [(even, 0), (odd, 1)] {
        assert!(kernel.environment().contains(family));
        let recursor = kernel.name_str(family, "rec");
        let Declaration::Recursor {
            num_motives,
            num_minors,
            num_params,
            num_indices: actual_indices,
            ..
        } = kernel.environment().get(recursor).unwrap()
        else {
            panic!("expected recursor");
        };
        assert_eq!((*num_motives, *num_minors, *num_params), (2, 0, 2));
        assert_eq!(*actual_indices, num_indices);
    }
}

#[test]
fn parameter_count_mismatch_is_typed_and_transactional() {
    let mut kernel = Kernel::new();
    let root = kernel.anon();
    let first = kernel.name_str(root, "FirstCount");
    let second = kernel.name_str(root, "SecondCount");
    let parameter = kernel.name_str(root, "p");
    let parameter_type = sort_one(&mut kernel);
    let result = sort_one(&mut kernel);
    let first_ty = kernel.pi(parameter, parameter_type, result, BinderInfo::Default);
    let families = [empty_family(first, first_ty), empty_family(second, result)];

    assert_eq!(
        kernel.add_mutual_inductive(&[], 1, &families),
        Err(KernelError::MutualInductiveParameterMismatch {
            family: second,
            parameter_index: 0,
        })
    );
    assert!(kernel.environment().is_empty());
}

#[test]
fn parameter_type_mismatch_is_typed_and_transactional() {
    let mut kernel = Kernel::new();
    let root = kernel.anon();
    let first = kernel.name_str(root, "FirstType");
    let second = kernel.name_str(root, "SecondType");
    let parameter = kernel.name_str(root, "p");
    let first_domain = sort_one(&mut kernel);
    let second_domain = kernel.sort_zero();
    let result = sort_one(&mut kernel);
    let first_ty = kernel.pi(parameter, first_domain, result, BinderInfo::Default);
    let second_ty = kernel.pi(parameter, second_domain, result, BinderInfo::Default);
    let families = [
        empty_family(first, first_ty),
        empty_family(second, second_ty),
    ];

    assert_eq!(
        kernel.add_mutual_inductive(&[], 1, &families),
        Err(KernelError::MutualInductiveParameterMismatch {
            family: second,
            parameter_index: 0,
        })
    );
    assert!(kernel.environment().is_empty());
}

#[test]
fn result_universe_mismatch_is_typed_and_transactional() {
    let mut kernel = Kernel::new();
    let root = kernel.anon();
    let first = kernel.name_str(root, "FirstUniverse");
    let second = kernel.name_str(root, "SecondUniverse");
    let first_ty = sort_one(&mut kernel);
    let second_ty = sort_two(&mut kernel);
    let families = [
        empty_family(first, first_ty),
        empty_family(second, second_ty),
    ];

    assert_eq!(
        kernel.add_mutual_inductive(&[], 0, &families),
        Err(KernelError::MutualInductiveResultUniverseMismatch { family: second })
    );
    assert!(kernel.environment().is_empty());
}

#[test]
fn duplicate_family_constructor_and_recursor_names_reject_before_publication() {
    fn duplicate_case(kind: &str) {
        let mut kernel = Kernel::new();
        let root = kernel.anon();
        let first = kernel.name_str(root, "DuplicateFirst");
        let first_recursor = kernel.name_str(first, "rec");
        let second = match kind {
            "family" => first,
            "recursor" => first_recursor,
            _ => kernel.name_str(root, "DuplicateSecond"),
        };
        let constructor = kernel.name_str(root, "sharedCtor");
        let ty = sort_one(&mut kernel);
        let first_constructors = if kind == "constructor" {
            vec![(constructor, ty)]
        } else {
            Vec::new()
        };
        let second_constructors = if kind == "constructor" {
            vec![(constructor, ty)]
        } else {
            Vec::new()
        };
        let expected = match kind {
            "family" => first,
            "constructor" => constructor,
            "recursor" => first_recursor,
            _ => unreachable!(),
        };
        let families = [
            InductiveFamilySpec::new(first, ty, first_constructors),
            InductiveFamilySpec::new(second, ty, second_constructors),
        ];

        assert_eq!(
            kernel.add_mutual_inductive(&[], 0, &families),
            Err(KernelError::DuplicateInductiveGroupName { name: expected }),
            "duplicate {kind} name"
        );
        assert!(kernel.environment().is_empty());
    }

    for kind in ["family", "constructor", "recursor"] {
        duplicate_case(kind);
    }
}

#[test]
fn existing_environment_name_collision_retains_declaration_exists_payload() {
    let mut kernel = Kernel::new();
    let root = kernel.anon();
    let occupied = kernel.name_str(root, "Occupied");
    let second = kernel.name_str(root, "FreshFamily");
    let prop = kernel.sort_zero();
    kernel
        .add_declaration(Declaration::Axiom {
            name: occupied,
            uparams: Vec::new(),
            ty: prop,
        })
        .expect("seed declaration admits");
    let before = declarations(&kernel);
    let family_ty = sort_one(&mut kernel);
    let families = [
        empty_family(occupied, family_ty),
        empty_family(second, family_ty),
    ];

    assert_eq!(
        kernel.add_mutual_inductive(&[], 0, &families),
        Err(KernelError::DeclarationExists { name: occupied })
    );
    assert_eq!(declarations(&kernel), before);
}

#[test]
fn singleton_error_payload_and_retry_behavior_are_preserved() {
    let mut kernel = Kernel::new();
    let root = kernel.anon();
    let family = kernel.name_str(root, "RetryFamily");
    let constructor = kernel.name_str(family, "mk");
    let family_ty = sort_one(&mut kernel);
    let wrong_result = kernel.sort_zero();
    let before = declarations(&kernel);

    assert_eq!(
        kernel.add_inductive(family, &[], 0, family_ty, &[(constructor, wrong_result)]),
        Err(KernelError::ConstructorResultMismatch {
            expected: family,
            ctor: constructor,
        })
    );
    assert_eq!(declarations(&kernel), before);

    let correct_result = kernel.const_(family, vec![]);
    kernel
        .add_inductive(family, &[], 0, family_ty, &[(constructor, correct_result)])
        .expect("the same names admit after a failed transaction");
    assert!(kernel.environment().contains(family));
    assert!(kernel.environment().contains(constructor));
    let recursor = kernel.name_str(family, "rec");
    assert!(kernel.environment().contains(recursor));
}

fn apply_all(kernel: &mut Kernel, mut head: ExprId, arguments: &[ExprId]) -> ExprId {
    for &argument in arguments {
        head = kernel.app(head, argument);
    }
    head
}

fn return_induction_hypothesis_minor(kernel: &mut Kernel, field_type: ExprId) -> ExprId {
    let root = kernel.anon();
    let field = kernel.name_str(root, "field");
    let ih = kernel.name_str(root, "ih");
    let result = kernel.bvar(0);
    let prop = kernel.sort_zero();
    let inner = kernel.lam(ih, prop, result, BinderInfo::Default);
    kernel.lam(field, field_type, inner, BinderInfo::Default)
}

#[test]
fn two_family_cross_recursion_has_global_contract_and_computes() {
    let mut kernel = Kernel::new();
    let root = kernel.anon();
    let even = kernel.name_str(root, "M2Even");
    let odd = kernel.name_str(root, "M2Odd");
    let even_zero = kernel.name_str(even, "zero");
    let even_step = kernel.name_str(even, "step");
    let odd_step = kernel.name_str(odd, "step");
    let even_rec = kernel.name_str(even, "rec");
    let odd_rec = kernel.name_str(odd, "rec");
    let family_type = sort_one(&mut kernel);
    let even_const = kernel.const_(even, vec![]);
    let odd_const = kernel.const_(odd, vec![]);
    let even_step_type = kernel.pi(root, odd_const, even_const, BinderInfo::Default);
    let odd_step_type = kernel.pi(root, even_const, odd_const, BinderInfo::Default);
    let families = [
        InductiveFamilySpec::new(
            even,
            family_type,
            vec![(even_zero, even_const), (even_step, even_step_type)],
        ),
        InductiveFamilySpec::new(odd, family_type, vec![(odd_step, odd_step_type)]),
    ];

    kernel
        .add_mutual_inductive(&[], 0, &families)
        .expect("cross-recursive group admits atomically");
    assert_group_contract(&mut kernel, &families, 0, &[0, 0], true);

    for (recursor, owned_rules) in [
        (even_rec, vec![even_zero, even_step]),
        (odd_rec, vec![odd_step]),
    ] {
        let declaration = kernel
            .environment()
            .get(recursor)
            .expect("recursor")
            .clone();
        let Declaration::Recursor {
            rec_rules,
            num_motives,
            num_minors,
            num_params,
            num_indices,
            ..
        } = &declaration
        else {
            panic!("expected recursor declaration");
        };
        assert_eq!((*num_motives, *num_minors), (2, 3));
        assert_eq!((*num_params, *num_indices), (0, 0));
        assert_eq!(
            rec_rules
                .iter()
                .map(|rule| rule.ctor_name)
                .collect::<Vec<_>>(),
            owned_rules
        );
        assert!(matches!(
            {
                let inferred = kernel.infer(declaration.ty()).unwrap();
                kernel.expr_node(inferred)
            },
            axeyum_lean_kernel::ExprNode::Sort(_)
        ));
    }

    let even_declaration = kernel.environment().get(even_rec).unwrap().clone();
    let levels = even_declaration
        .uparams()
        .iter()
        .map(|&parameter| kernel.level_param(parameter))
        .collect::<Vec<_>>();
    let even_motive = kernel.fvar(100);
    let odd_motive = kernel.fvar(101);
    let zero_minor = kernel.fvar(102);
    let even_minor = return_induction_hypothesis_minor(&mut kernel, odd_const);
    let odd_minor = return_induction_hypothesis_minor(&mut kernel, even_const);
    let zero_value = kernel.const_(even_zero, vec![]);
    let odd_value = {
        let head = kernel.const_(odd_step, vec![]);
        kernel.app(head, zero_value)
    };
    let even_value = {
        let head = kernel.const_(even_step, vec![]);
        kernel.app(head, odd_value)
    };
    let recursor = kernel.const_(even_rec, levels);
    let application = apply_all(
        &mut kernel,
        recursor,
        &[
            even_motive,
            odd_motive,
            zero_minor,
            even_minor,
            odd_minor,
            even_value,
        ],
    );
    assert_eq!(kernel.whnf(application), zero_minor);
}

fn declare_index_type(kernel: &mut Kernel, label: &str) -> (NameId, NameId, NameId) {
    let root = kernel.anon();
    let family = kernel.name_str(root, label);
    let zero = kernel.name_str(family, "zero");
    let succ = kernel.name_str(family, "succ");
    let ty = sort_one(kernel);
    let family_const = kernel.const_(family, vec![]);
    let succ_ty = kernel.pi(root, family_const, family_const, BinderInfo::Default);
    kernel
        .add_inductive(family, &[], 0, ty, &[(zero, family_const), (succ, succ_ty)])
        .expect("index type admits");
    (family, zero, succ)
}

fn return_last_minor(kernel: &mut Kernel, domains: &[ExprId]) -> ExprId {
    let root = kernel.anon();
    let binder = kernel.name_str(root, "argument");
    let mut body = kernel.bvar(0);
    for &domain in domains.iter().rev() {
        body = kernel.lam(binder, domain, body, BinderInfo::Default);
    }
    body
}

fn recursor_levels(kernel: &mut Kernel, recursor: NameId) -> Vec<axeyum_lean_kernel::LevelId> {
    kernel
        .environment()
        .get(recursor)
        .unwrap()
        .uparams()
        .to_vec()
        .into_iter()
        .map(|parameter| kernel.level_param(parameter))
        .collect()
}

#[test]
fn indexed_cross_recursion_uses_target_indices_and_computes() {
    let mut kernel = Kernel::new();
    let root = kernel.anon();
    let (index, index_zero, index_succ) = declare_index_type(&mut kernel, "M2Index");
    let index_const = kernel.const_(index, vec![]);
    let index_zero_value = kernel.const_(index_zero, vec![]);
    let index_succ_const = kernel.const_(index_succ, vec![]);
    let even = kernel.name_str(root, "M2IndexedEven");
    let odd = kernel.name_str(root, "M2IndexedOdd");
    let even_zero = kernel.name_str(even, "zero");
    let even_step = kernel.name_str(even, "step");
    let odd_step = kernel.name_str(odd, "step");
    let even_rec = kernel.name_str(even, "rec");
    let even_const = kernel.const_(even, vec![]);
    let odd_const = kernel.const_(odd, vec![]);
    let result_sort = sort_one(&mut kernel);
    let family_type = kernel.pi(root, index_const, result_sort, BinderInfo::Default);
    let even_zero_type = kernel.app(even_const, index_zero_value);
    let even_step_type = {
        let index_for_result = kernel.bvar(1);
        let next_index = kernel.app(index_succ_const, index_for_result);
        let result = kernel.app(even_const, next_index);
        let index_for_field = kernel.bvar(0);
        let field_type = kernel.app(odd_const, index_for_field);
        let inner = kernel.pi(root, field_type, result, BinderInfo::Default);
        kernel.pi(root, index_const, inner, BinderInfo::Default)
    };
    let odd_step_type = {
        let index_for_result = kernel.bvar(1);
        let next_index = kernel.app(index_succ_const, index_for_result);
        let result = kernel.app(odd_const, next_index);
        let index_for_field = kernel.bvar(0);
        let field_type = kernel.app(even_const, index_for_field);
        let inner = kernel.pi(root, field_type, result, BinderInfo::Default);
        kernel.pi(root, index_const, inner, BinderInfo::Default)
    };
    let families = [
        InductiveFamilySpec::new(
            even,
            family_type,
            vec![(even_zero, even_zero_type), (even_step, even_step_type)],
        ),
        InductiveFamilySpec::new(odd, family_type, vec![(odd_step, odd_step_type)]),
    ];
    kernel
        .add_mutual_inductive(&[], 0, &families)
        .expect("indexed cross recursion admits");
    assert_group_contract(&mut kernel, &families, 0, &[1, 1], true);

    let levels = recursor_levels(&mut kernel, even_rec);
    let even_motive = kernel.fvar(200);
    let odd_motive = kernel.fvar(201);
    let zero_minor = kernel.fvar(202);
    let even_minor = return_last_minor(&mut kernel, &[index_const, odd_const, result_sort]);
    let odd_minor = return_last_minor(&mut kernel, &[index_const, even_const, result_sort]);
    let zero_value = kernel.const_(even_zero, vec![]);
    let next_zero = kernel.app(index_succ_const, index_zero_value);
    let odd_value = {
        let head = kernel.const_(odd_step, vec![]);
        apply_all(&mut kernel, head, &[index_zero_value, zero_value])
    };
    let even_value = {
        let head = kernel.const_(even_step, vec![]);
        apply_all(&mut kernel, head, &[next_zero, odd_value])
    };
    let final_index = kernel.app(index_succ_const, next_zero);
    let recursor = kernel.const_(even_rec, levels);
    let application = apply_all(
        &mut kernel,
        recursor,
        &[
            even_motive,
            odd_motive,
            zero_minor,
            even_minor,
            odd_minor,
            final_index,
            even_value,
        ],
    );
    assert_eq!(kernel.whnf(application), zero_minor);
}

#[test]
fn higher_order_cross_recursion_preserves_the_telescope_and_computes() {
    let mut kernel = Kernel::new();
    let root = kernel.anon();
    let left = kernel.name_str(root, "M2HigherLeft");
    let right = kernel.name_str(root, "M2HigherRight");
    let left_node = kernel.name_str(left, "node");
    let right_base = kernel.name_str(right, "base");
    let left_rec = kernel.name_str(left, "rec");
    let family_type = sort_one(&mut kernel);
    let left_const = kernel.const_(left, vec![]);
    let right_const = kernel.const_(right, vec![]);
    let prop = kernel.sort_zero();
    let function_field = kernel.pi(root, prop, right_const, BinderInfo::StrictImplicit);
    let left_node_type = kernel.pi(root, function_field, left_const, BinderInfo::Default);
    let families = [
        InductiveFamilySpec::new(left, family_type, vec![(left_node, left_node_type)]),
        InductiveFamilySpec::new(right, family_type, vec![(right_base, right_const)]),
    ];
    kernel
        .add_mutual_inductive(&[], 0, &families)
        .expect("higher-order cross recursion admits");
    assert_group_contract(&mut kernel, &families, 0, &[0, 0], true);

    let levels = recursor_levels(&mut kernel, left_rec);
    let left_motive = kernel.fvar(300);
    let right_motive = kernel.fvar(301);
    let result = kernel.fvar(302);
    let witness = kernel.fvar(303);
    let left_minor = {
        let ih = kernel.bvar(0);
        let applied = kernel.app(ih, witness);
        let inner = kernel.lam(root, prop, applied, BinderInfo::Default);
        kernel.lam(root, function_field, inner, BinderInfo::Default)
    };
    let right_minor = result;
    let right_base_value = kernel.const_(right_base, vec![]);
    let field = kernel.lam(root, prop, right_base_value, BinderInfo::StrictImplicit);
    let major = {
        let head = kernel.const_(left_node, vec![]);
        kernel.app(head, field)
    };
    let recursor = kernel.const_(left_rec, levels);
    let application = apply_all(
        &mut kernel,
        recursor,
        &[left_motive, right_motive, left_minor, right_minor, major],
    );
    assert_eq!(kernel.whnf(application), result);
}

fn count_constant(kernel: &Kernel, expression: ExprId, target: NameId) -> usize {
    match kernel.expr_node(expression).clone() {
        axeyum_lean_kernel::ExprNode::Const(name, _) => usize::from(name == target),
        axeyum_lean_kernel::ExprNode::BVar(_)
        | axeyum_lean_kernel::ExprNode::FVar(_)
        | axeyum_lean_kernel::ExprNode::Sort(_)
        | axeyum_lean_kernel::ExprNode::Lit(_) => 0,
        axeyum_lean_kernel::ExprNode::Proj(_, _, structure) => {
            count_constant(kernel, structure, target)
        }
        axeyum_lean_kernel::ExprNode::App(function, argument) => {
            count_constant(kernel, function, target) + count_constant(kernel, argument, target)
        }
        axeyum_lean_kernel::ExprNode::Lam(_, ty, body, _)
        | axeyum_lean_kernel::ExprNode::Pi(_, ty, body, _) => {
            count_constant(kernel, ty, target) + count_constant(kernel, body, target)
        }
        axeyum_lean_kernel::ExprNode::Let(_, ty, value, body) => {
            count_constant(kernel, ty, target)
                + count_constant(kernel, value, target)
                + count_constant(kernel, body, target)
        }
    }
}

#[test]
fn three_family_cycle_mixed_self_cross_and_multiple_targets_are_global() {
    let mut kernel = Kernel::new();
    let root = kernel.anon();
    let names = ["M2CycleA", "M2CycleB", "M2CycleC"].map(|label| kernel.name_str(root, label));
    let constants = names.map(|name| kernel.const_(name, vec![]));
    let base = kernel.name_str(names[0], "base");
    let node = kernel.name_str(names[0], "node");
    let b_step = kernel.name_str(names[1], "step");
    let c_step = kernel.name_str(names[2], "step");
    let result_sort = sort_one(&mut kernel);
    let node_type = {
        let mut ty = constants[0];
        for domain in constants.iter().rev() {
            ty = kernel.pi(root, *domain, ty, BinderInfo::Default);
        }
        ty
    };
    let b_type = kernel.pi(root, constants[2], constants[1], BinderInfo::Default);
    let c_type = kernel.pi(root, constants[0], constants[2], BinderInfo::Default);
    let families = [
        InductiveFamilySpec::new(
            names[0],
            result_sort,
            vec![(base, constants[0]), (node, node_type)],
        ),
        InductiveFamilySpec::new(names[1], result_sort, vec![(b_step, b_type)]),
        InductiveFamilySpec::new(names[2], result_sort, vec![(c_step, c_type)]),
    ];
    kernel
        .add_mutual_inductive(&[], 0, &families)
        .expect("three-family mixed cycle admits");
    assert_group_contract(&mut kernel, &families, 0, &[0, 0, 0], true);

    let recursors = names.map(|name| kernel.name_str(name, "rec"));
    let Declaration::Recursor {
        rec_rules,
        num_motives,
        num_minors,
        ..
    } = kernel.environment().get(recursors[0]).unwrap()
    else {
        panic!("expected recursor");
    };
    assert_eq!((*num_motives, *num_minors), (3, 4));
    let node_rule = rec_rules
        .iter()
        .find(|rule| rule.ctor_name == node)
        .expect("node rule");
    for recursor in recursors {
        assert_eq!(count_constant(&kernel, node_rule.value, recursor), 1);
    }
}

#[test]
fn three_families_may_have_zero_one_and_two_indices() {
    let mut kernel = Kernel::new();
    let root = kernel.anon();
    let result = sort_one(&mut kernel);
    let index_domain = kernel.sort_zero();
    let families_names =
        ["M2Index0", "M2Index1", "M2Index2"].map(|label| kernel.name_str(root, label));
    let one_index = kernel.pi(root, index_domain, result, BinderInfo::Default);
    let two_indices = {
        let inner = kernel.pi(root, index_domain, result, BinderInfo::Default);
        kernel.pi(root, index_domain, inner, BinderInfo::Implicit)
    };
    let families = [
        empty_family(families_names[0], result),
        empty_family(families_names[1], one_index),
        empty_family(families_names[2], two_indices),
    ];
    kernel
        .add_mutual_inductive(&[], 0, &families)
        .expect("independent family index suffixes admit");
    assert_group_contract(&mut kernel, &families, 0, &[0, 1, 2], false);
    for (family, expected) in families_names.into_iter().zip([0, 1, 2]) {
        let recursor = kernel.name_str(family, "rec");
        let Declaration::Recursor {
            num_motives,
            num_minors,
            num_indices,
            ..
        } = kernel.environment().get(recursor).unwrap()
        else {
            panic!("expected recursor");
        };
        assert_eq!((*num_motives, *num_minors), (3, 0));
        assert_eq!(*num_indices, expected);
    }
}

#[test]
fn empty_constructor_family_still_receives_a_global_recursor() {
    let mut kernel = Kernel::new();
    let root = kernel.anon();
    let empty = kernel.name_str(root, "M2EmptyFamily");
    let inhabited = kernel.name_str(root, "M2InhabitedFamily");
    let base = kernel.name_str(inhabited, "base");
    let ty = sort_one(&mut kernel);
    let inhabited_const = kernel.const_(inhabited, vec![]);
    let families = [
        empty_family(empty, ty),
        InductiveFamilySpec::new(inhabited, ty, vec![(base, inhabited_const)]),
    ];
    kernel
        .add_mutual_inductive(&[], 0, &families)
        .expect("empty family in a nonempty group admits");
    assert_group_contract(&mut kernel, &families, 0, &[0, 0], false);
    let empty_rec = kernel.name_str(empty, "rec");
    let Declaration::Recursor {
        rec_rules,
        num_motives,
        num_minors,
        ..
    } = kernel.environment().get(empty_rec).unwrap()
    else {
        panic!("expected recursor");
    };
    assert!(rec_rules.is_empty());
    assert_eq!((*num_motives, *num_minors), (2, 1));
}

#[test]
fn mutual_predicates_eliminate_only_to_prop_and_never_gain_k_like_levels() {
    let mut kernel = Kernel::new();
    let root = kernel.anon();
    let left = kernel.name_str(root, "M2PredLeft");
    let right = kernel.name_str(root, "M2PredRight");
    let left_base = kernel.name_str(left, "base");
    let left_step = kernel.name_str(left, "step");
    let right_step = kernel.name_str(right, "step");
    let prop = kernel.sort_zero();
    let left_const = kernel.const_(left, vec![]);
    let right_const = kernel.const_(right, vec![]);
    let left_step_type = kernel.pi(root, right_const, left_const, BinderInfo::Default);
    let right_step_type = kernel.pi(root, left_const, right_const, BinderInfo::Default);
    let families = [
        InductiveFamilySpec::new(
            left,
            prop,
            vec![(left_base, left_const), (left_step, left_step_type)],
        ),
        InductiveFamilySpec::new(right, prop, vec![(right_step, right_step_type)]),
    ];
    kernel
        .add_mutual_inductive(&[], 0, &families)
        .expect("mutual predicates admit with Prop motives");
    assert_group_contract(&mut kernel, &families, 0, &[0, 0], true);
    for family in [left, right] {
        let recursor = kernel.name_str(family, "rec");
        let declaration = kernel.environment().get(recursor).unwrap();
        assert!(declaration.uparams().is_empty());
        let Declaration::Recursor {
            num_motives,
            num_minors,
            ..
        } = declaration
        else {
            panic!("expected recursor");
        };
        assert_eq!((*num_motives, *num_minors), (2, 3));
    }
}

#[test]
fn cross_family_negative_domain_rejects_before_publication() {
    let mut kernel = Kernel::new();
    let root = kernel.anon();
    let left = kernel.name_str(root, "M2NegativeLeft");
    let right = kernel.name_str(root, "M2NegativeRight");
    let bad = kernel.name_str(left, "bad");
    let ty = sort_one(&mut kernel);
    let left_const = kernel.const_(left, vec![]);
    let right_const = kernel.const_(right, vec![]);
    let negative = kernel.pi(root, right_const, left_const, BinderInfo::Default);
    let bad_type = kernel.pi(root, negative, left_const, BinderInfo::Default);
    let families = [
        InductiveFamilySpec::new(left, ty, vec![(bad, bad_type)]),
        empty_family(right, ty),
    ];
    let before = declarations(&kernel);
    assert_eq!(
        kernel.add_mutual_inductive(&[], 0, &families),
        Err(KernelError::NonPositiveInductiveOccurrence {
            inductive: left,
            ctor: bad,
            field_index: 0,
        })
    );
    assert_eq!(declarations(&kernel), before);
}

#[test]
fn cross_family_incomplete_application_rejects_before_publication() {
    let mut kernel = Kernel::new();
    let root = kernel.anon();
    let left = kernel.name_str(root, "M2InvalidLeft");
    let right = kernel.name_str(root, "M2InvalidRight");
    let bad = kernel.name_str(left, "bad");
    let result = sort_one(&mut kernel);
    let index_domain = kernel.sort_zero();
    let left_const = kernel.const_(left, vec![]);
    let right_const = kernel.const_(right, vec![]);
    let right_type = kernel.pi(root, index_domain, result, BinderInfo::Default);
    let bad_type = kernel.pi(root, right_const, left_const, BinderInfo::Default);
    let families = [
        InductiveFamilySpec::new(left, result, vec![(bad, bad_type)]),
        empty_family(right, right_type),
    ];
    let before = declarations(&kernel);
    assert_eq!(
        kernel.add_mutual_inductive(&[], 0, &families),
        Err(KernelError::InvalidInductiveOccurrence {
            inductive: left,
            ctor: bad,
            field_index: 0,
        })
    );
    assert_eq!(declarations(&kernel), before);
}
