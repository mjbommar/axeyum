//! TL2.5 structure-eta gate.
//!
//! Lean's kernel applies structure eta only to exactly saturated constructor
//! applications whose parent inductive has one constructor, no indices, and no
//! recursive fields. These controls exercise the positive rule, symmetry,
//! dependent and universe-parametric fields, and the indexed/recursive/type-
//! mismatch exclusions that keep the rule from manufacturing equality.

use axeyum_lean_kernel::{BinderInfo, Declaration, ExprId, Kernel, NameId, ReducibilityHint};

fn pi_telescope(kernel: &mut Kernel, locals: &[(u64, NameId, ExprId)], body: ExprId) -> ExprId {
    let mut result = body;
    for &(fvar, name, ty) in locals.iter().rev() {
        result = kernel.abstract_fvars(result, &[fvar]);
        result = kernel.pi(name, ty, result, BinderInfo::Default);
    }
    result
}

fn add_axiom(kernel: &mut Kernel, name: NameId, ty: ExprId) {
    kernel
        .add_declaration(Declaration::Axiom {
            name,
            uparams: vec![],
            ty,
        })
        .expect("test axiom should admit");
}

struct AtomFixture {
    atom: NameId,
    first: NameId,
}

fn add_atom_fixture(kernel: &mut Kernel) -> AtomFixture {
    let anon = kernel.anon();
    let atom = kernel.name_str(anon, "EtaAtom");
    let first = kernel.name_str(anon, "etaFirst");
    let zero = kernel.level_zero();
    let one = kernel.level_succ(zero);
    let sort_one = kernel.sort(one);
    add_axiom(kernel, atom, sort_one);
    let atom_type = kernel.const_(atom, vec![]);
    add_axiom(kernel, first, atom_type);
    AtomFixture { atom, first }
}

struct PairFixture {
    name: NameId,
    ctor: NameId,
    value: NameId,
}

fn add_pair_fixture(kernel: &mut Kernel, atom: NameId) -> PairFixture {
    let anon = kernel.anon();
    let name = kernel.name_str(anon, "EtaPair");
    let ctor = kernel.name_str(name, "mk");
    let value = kernel.name_str(anon, "etaPairValue");
    let left_name = kernel.name_str(anon, "left");
    let right_name = kernel.name_str(anon, "right");
    let atom_type = kernel.const_(atom, vec![]);
    let pair_type = {
        let zero = kernel.level_zero();
        let one = kernel.level_succ(zero);
        kernel.sort(one)
    };
    let pair_const = kernel.const_(name, vec![]);
    let ctor_type = pi_telescope(
        kernel,
        &[(100, left_name, atom_type), (101, right_name, atom_type)],
        pair_const,
    );
    kernel
        .add_inductive(name, &[], 0, pair_type, &[(ctor, ctor_type)])
        .expect("pair structure should admit");
    add_axiom(kernel, value, pair_const);
    PairFixture { name, ctor, value }
}

#[test]
fn rebuilt_structure_is_definitionally_equal_in_both_directions() {
    let mut kernel = Kernel::new();
    let atom = add_atom_fixture(&mut kernel);
    let pair = add_pair_fixture(&mut kernel, atom.atom);
    let value = kernel.const_(pair.value, vec![]);
    let left = kernel.proj(pair.name, 0, value);
    let right = kernel.proj(pair.name, 1, value);
    let ctor = kernel.const_(pair.ctor, vec![]);
    let rebuilt = kernel.app(ctor, left);
    let rebuilt = kernel.app(rebuilt, right);

    assert!(kernel.def_eq(value, rebuilt));
    assert!(kernel.def_eq(rebuilt, value));

    let anon = kernel.anon();
    let theorem = kernel.name_str(anon, "etaPairRebuild");
    let pair_type = kernel.const_(pair.name, vec![]);
    kernel
        .add_declaration(Declaration::Definition {
            name: theorem,
            uparams: vec![],
            ty: pair_type,
            value: rebuilt,
            hint: ReducibilityHint::Regular(0),
        })
        .expect("eta-rebuilt structure should pass the declaration gate");
}

#[test]
fn wrong_field_and_wrong_structure_type_do_not_become_equal() {
    let mut kernel = Kernel::new();
    let atom = add_atom_fixture(&mut kernel);
    let pair = add_pair_fixture(&mut kernel, atom.atom);
    let value = kernel.const_(pair.value, vec![]);
    let left = kernel.proj(pair.name, 0, value);
    let ctor = kernel.const_(pair.ctor, vec![]);
    let under_applied = kernel.app(ctor, left);
    assert!(!kernel.def_eq(value, under_applied));
    let wrong_field = kernel.app(ctor, left);
    let wrong_field = kernel.app(wrong_field, left);
    assert!(!kernel.def_eq(value, wrong_field));
    assert!(!kernel.def_eq(wrong_field, value));

    let anon = kernel.anon();
    let other_name = kernel.name_str(anon, "OtherEtaPair");
    let other_ctor = kernel.name_str(other_name, "mk");
    let atom_type = kernel.const_(atom.atom, vec![]);
    let other_type = {
        let zero = kernel.level_zero();
        let one = kernel.level_succ(zero);
        kernel.sort(one)
    };
    let other_const = kernel.const_(other_name, vec![]);
    let other_ctor_type = pi_telescope(
        &mut kernel,
        &[(110, anon, atom_type), (111, anon, atom_type)],
        other_const,
    );
    kernel
        .add_inductive(
            other_name,
            &[],
            0,
            other_type,
            &[(other_ctor, other_ctor_type)],
        )
        .unwrap();
    let other = kernel.const_(other_ctor, vec![]);
    let other = kernel.app(other, left);
    let right = kernel.proj(pair.name, 1, value);
    let other = kernel.app(other, right);
    assert!(!kernel.def_eq(value, other));
}

#[test]
fn zero_field_structure_applies_but_multi_constructor_family_does_not() {
    let mut kernel = Kernel::new();
    let anon = kernel.anon();
    let sort_one = {
        let zero = kernel.level_zero();
        let one = kernel.level_succ(zero);
        kernel.sort(one)
    };

    let unit_name = kernel.name_str(anon, "EtaUnit");
    let unit_ctor = kernel.name_str(unit_name, "mk");
    let unit_value_name = kernel.name_str(anon, "etaUnitValue");
    let unit_const = kernel.const_(unit_name, vec![]);
    kernel
        .add_inductive(unit_name, &[], 0, sort_one, &[(unit_ctor, unit_const)])
        .unwrap();
    add_axiom(&mut kernel, unit_value_name, unit_const);
    let unit_value = kernel.const_(unit_value_name, vec![]);
    let unit_constructor = kernel.const_(unit_ctor, vec![]);
    assert!(kernel.def_eq(unit_value, unit_constructor));
    assert!(kernel.def_eq(unit_constructor, unit_value));

    let choice_name = kernel.name_str(anon, "EtaChoice");
    let first_ctor = kernel.name_str(choice_name, "first");
    let second_ctor = kernel.name_str(choice_name, "second");
    let choice_value_name = kernel.name_str(anon, "etaChoiceValue");
    let choice_const = kernel.const_(choice_name, vec![]);
    kernel
        .add_inductive(
            choice_name,
            &[],
            0,
            sort_one,
            &[(first_ctor, choice_const), (second_ctor, choice_const)],
        )
        .unwrap();
    add_axiom(&mut kernel, choice_value_name, choice_const);
    let choice_value = kernel.const_(choice_value_name, vec![]);
    let first_constructor = kernel.const_(first_ctor, vec![]);
    assert!(!kernel.def_eq(choice_value, first_constructor));
    assert!(!kernel.def_eq(first_constructor, choice_value));
}

#[test]
fn universe_parameterized_structure_eta_preserves_constructor_parameters() {
    let mut kernel = Kernel::new();
    let atom = add_atom_fixture(&mut kernel);
    let anon = kernel.anon();
    let box_name = kernel.name_str(anon, "EtaBox");
    let ctor_name = kernel.name_str(box_name, "mk");
    let value_name = kernel.name_str(anon, "etaBoxValue");
    let u_name = kernel.name_str(anon, "u");
    let alpha_name = kernel.name_str(anon, "Alpha");
    let field_name = kernel.name_str(anon, "value");
    let u = kernel.level_param(u_name);
    let sort_u = kernel.sort(u);
    let alpha = kernel.fvar(200);
    let box_const = kernel.const_(box_name, vec![u]);
    let box_alpha = kernel.app(box_const, alpha);
    let ind_type = {
        let succ_u = kernel.level_succ(u);
        let result_sort = kernel.sort(succ_u);
        pi_telescope(&mut kernel, &[(200, alpha_name, sort_u)], result_sort)
    };
    let ctor_type = pi_telescope(
        &mut kernel,
        &[(200, alpha_name, sort_u), (201, field_name, alpha)],
        box_alpha,
    );
    kernel
        .add_inductive(box_name, &[u_name], 1, ind_type, &[(ctor_name, ctor_type)])
        .unwrap();

    let zero = kernel.level_zero();
    let one = kernel.level_succ(zero);
    let atom_type = kernel.const_(atom.atom, vec![]);
    let box_at_atom = {
        let head = kernel.const_(box_name, vec![one]);
        kernel.app(head, atom_type)
    };
    add_axiom(&mut kernel, value_name, box_at_atom);
    let value = kernel.const_(value_name, vec![]);
    let field = kernel.proj(box_name, 0, value);
    let rebuilt = {
        let ctor = kernel.const_(ctor_name, vec![one]);
        let ctor = kernel.app(ctor, atom_type);
        kernel.app(ctor, field)
    };
    assert!(kernel.def_eq(value, rebuilt));
    assert!(kernel.def_eq(rebuilt, value));
}

#[test]
fn dependent_field_structure_eta_uses_prior_projection() {
    let mut kernel = Kernel::new();
    let atom = add_atom_fixture(&mut kernel);
    let anon = kernel.anon();
    let family_name = kernel.name_str(anon, "EtaFamily");
    let element_name = kernel.name_str(anon, "etaElement");
    let dep_name = kernel.name_str(anon, "EtaDependent");
    let ctor_name = kernel.name_str(dep_name, "mk");
    let value_name = kernel.name_str(anon, "etaDependentValue");
    let atom_type = kernel.const_(atom.atom, vec![]);
    let sort_one = {
        let zero = kernel.level_zero();
        let one = kernel.level_succ(zero);
        kernel.sort(one)
    };
    let family_type = kernel.pi(anon, atom_type, sort_one, BinderInfo::Default);
    add_axiom(&mut kernel, family_name, family_type);
    let family = kernel.const_(family_name, vec![]);
    let first_value = kernel.const_(atom.first, vec![]);
    let element_type = kernel.app(family, first_value);
    add_axiom(&mut kernel, element_name, element_type);

    let dep_const = kernel.const_(dep_name, vec![]);
    let first = kernel.fvar(300);
    let second_type = kernel.app(family, first);
    let first_name = kernel.name_str(anon, "first");
    let second_name = kernel.name_str(anon, "second");
    let ctor_type = pi_telescope(
        &mut kernel,
        &[
            (300, first_name, atom_type),
            (301, second_name, second_type),
        ],
        dep_const,
    );
    kernel
        .add_inductive(dep_name, &[], 0, sort_one, &[(ctor_name, ctor_type)])
        .unwrap();
    add_axiom(&mut kernel, value_name, dep_const);

    let value = kernel.const_(value_name, vec![]);
    let first = kernel.proj(dep_name, 0, value);
    let second = kernel.proj(dep_name, 1, value);
    assert_eq!(kernel.infer(second).unwrap(), kernel.app(family, first));
    let ctor = kernel.const_(ctor_name, vec![]);
    let rebuilt = kernel.app(ctor, first);
    let rebuilt = kernel.app(rebuilt, second);
    assert!(kernel.def_eq(value, rebuilt));
}

#[test]
fn indexed_single_constructor_family_is_not_a_structure_eta_target() {
    let mut kernel = Kernel::new();
    let atom = add_atom_fixture(&mut kernel);
    let anon = kernel.anon();
    let indexed_name = kernel.name_str(anon, "EtaIndexed");
    let ctor_name = kernel.name_str(indexed_name, "mk");
    let value_name = kernel.name_str(anon, "etaIndexedValue");
    let atom_type = kernel.const_(atom.atom, vec![]);
    let sort_one = {
        let zero = kernel.level_zero();
        let one = kernel.level_succ(zero);
        kernel.sort(one)
    };
    let indexed_type = kernel.pi(anon, atom_type, sort_one, BinderInfo::Default);
    let index = kernel.const_(atom.first, vec![]);
    let indexed_at_first = {
        let head = kernel.const_(indexed_name, vec![]);
        kernel.app(head, index)
    };
    let field_name = kernel.name_str(anon, "field");
    let ctor_type = pi_telescope(
        &mut kernel,
        &[(400, field_name, atom_type)],
        indexed_at_first,
    );
    kernel
        .add_inductive(
            indexed_name,
            &[],
            0,
            indexed_type,
            &[(ctor_name, ctor_type)],
        )
        .unwrap();
    add_axiom(&mut kernel, value_name, indexed_at_first);
    let value = kernel.const_(value_name, vec![]);
    let field = kernel.proj(indexed_name, 0, value);
    let ctor = kernel.const_(ctor_name, vec![]);
    let rebuilt = kernel.app(ctor, field);
    assert_eq!(kernel.infer(rebuilt).unwrap(), indexed_at_first);
    assert!(!kernel.def_eq(value, rebuilt));
    assert!(!kernel.def_eq(rebuilt, value));
}

#[test]
fn recursive_single_constructor_family_is_not_a_structure_eta_target() {
    let mut kernel = Kernel::new();
    let anon = kernel.anon();
    let recursive_name = kernel.name_str(anon, "EtaRecursive");
    let ctor_name = kernel.name_str(recursive_name, "mk");
    let value_name = kernel.name_str(anon, "etaRecursiveValue");
    let recursive_type = {
        let zero = kernel.level_zero();
        let one = kernel.level_succ(zero);
        kernel.sort(one)
    };
    let recursive_const = kernel.const_(recursive_name, vec![]);
    let ctor_type = kernel.pi(anon, recursive_const, recursive_const, BinderInfo::Default);
    kernel
        .add_inductive(
            recursive_name,
            &[],
            0,
            recursive_type,
            &[(ctor_name, ctor_type)],
        )
        .unwrap();
    add_axiom(&mut kernel, value_name, recursive_const);
    let value = kernel.const_(value_name, vec![]);
    let field = kernel.proj(recursive_name, 0, value);
    let ctor = kernel.const_(ctor_name, vec![]);
    let rebuilt = kernel.app(ctor, field);
    assert_eq!(kernel.infer(rebuilt).unwrap(), recursive_const);
    assert!(!kernel.def_eq(value, rebuilt));
    assert!(!kernel.def_eq(rebuilt, value));

    match kernel.environment().get(recursive_name).unwrap() {
        Declaration::Inductive { is_recursive, .. } => assert!(*is_recursive),
        declaration => panic!("expected inductive metadata, got {declaration:?}"),
    }
}
