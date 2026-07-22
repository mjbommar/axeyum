//! TL2.13 M1 ordered mutual-inductive representation and transaction gates.
//!
//! M1 intentionally does not admit a multi-family group. These tests freeze
//! singleton identity/behavior, deterministic group preflight errors, and exact
//! environment rollback before M2 changes positivity or recursor semantics.

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
fn valid_dependent_parameters_and_per_family_indices_reach_policy_decline() {
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
    let before = declarations(&kernel);

    assert_eq!(
        kernel.add_mutual_inductive(&[], 2, &families),
        Err(KernelError::MutualInductiveNotSupported { family_count: 2 })
    );
    assert_eq!(declarations(&kernel), before);
    for family in families {
        assert!(!kernel.environment().contains(family.name));
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
