//! TL2.3 gate for checked Lean structure metadata and dependent projection
//! type inference.
//!
//! Constructor projection reduction and structure eta are deliberately absent;
//! those are independently gated TL2.4 and TL2.5 semantics.

use axeyum_lean_kernel::{
    BinderInfo, Declaration, ExprId, Kernel, KernelError, LocalContext, LocalDecl, NameId,
};

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

struct DependentStructure {
    name: NameId,
    ctor: NameId,
}

fn add_dependent_structure(kernel: &mut Kernel) -> DependentStructure {
    let anon = kernel.anon();
    let name = kernel.name_str(anon, "DependentPair");
    let ctor = kernel.name_str(name, "mk");
    let alpha_name = kernel.name_str(anon, "Alpha");
    let predicate_name = kernel.name_str(anon, "predicate");
    let first_name = kernel.name_str(anon, "first");
    let second_name = kernel.name_str(anon, "second");
    let sort_zero = kernel.sort_zero();
    let sort_one = {
        let zero = kernel.level_zero();
        let one = kernel.level_succ(zero);
        kernel.sort(one)
    };

    let alpha_fvar = 100;
    let predicate_fvar = 101;
    let first_fvar = 102;
    let second_fvar = 103;
    let alpha = kernel.fvar(alpha_fvar);
    let predicate = kernel.fvar(predicate_fvar);
    let first = kernel.fvar(first_fvar);
    let predicate_type = kernel.pi(anon, alpha, sort_zero, BinderInfo::Default);

    let ind_type = pi_telescope(
        kernel,
        &[
            (alpha_fvar, alpha_name, sort_one),
            (predicate_fvar, predicate_name, predicate_type),
        ],
        sort_one,
    );
    let ind_const = kernel.const_(name, vec![]);
    let applied_to_alpha = kernel.app(ind_const, alpha);
    let result = kernel.app(applied_to_alpha, predicate);
    let second_type = kernel.app(predicate, first);
    let ctor_type = pi_telescope(
        kernel,
        &[
            (alpha_fvar, alpha_name, sort_one),
            (predicate_fvar, predicate_name, predicate_type),
            (first_fvar, first_name, alpha),
            (second_fvar, second_name, second_type),
        ],
        result,
    );
    kernel
        .add_inductive(name, &[], 2, ind_type, &[(ctor, ctor_type)])
        .expect("dependent structure should admit");
    DependentStructure { name, ctor }
}

#[test]
fn parameterized_dependent_second_field_infers_from_the_first_projection() {
    let mut kernel = Kernel::new();
    let structure = add_dependent_structure(&mut kernel);
    let anon = kernel.anon();
    let predicate_name = kernel.name_str(anon, "identityPredicate");
    let value_name = kernel.name_str(anon, "dependentValue");
    let theorem_name = kernel.name_str(anon, "selectedSecond");
    let prop = kernel.sort_zero();
    let predicate = {
        let body = kernel.bvar(0);
        kernel.lam(predicate_name, prop, body, BinderInfo::Default)
    };
    let structure_type = {
        let head = kernel.const_(structure.name, vec![]);
        let at_prop = kernel.app(head, prop);
        kernel.app(at_prop, predicate)
    };
    add_axiom(&mut kernel, value_name, structure_type);
    let value = kernel.const_(value_name, vec![]);

    let first = kernel.proj(structure.name, 0, value);
    let second = kernel.proj(structure.name, 1, value);
    assert_eq!(kernel.infer(first).unwrap(), prop);
    let expected_second = kernel.app(predicate, first);
    assert_eq!(kernel.infer(second).unwrap(), expected_second);
    assert!(kernel.def_eq(expected_second, first));

    kernel
        .add_declaration(Declaration::Definition {
            name: theorem_name,
            uparams: vec![],
            ty: expected_second,
            value: second,
            hint: axeyum_lean_kernel::ReducibilityHint::Regular(0),
        })
        .expect("a well-typed dependent projection should enter a declaration");

    match kernel.environment().get(structure.name).unwrap() {
        Declaration::Inductive {
            num_params,
            num_indices,
            ctor_names,
            ..
        } => {
            assert_eq!((*num_params, *num_indices), (2, 0));
            assert_eq!(ctor_names, &[structure.ctor]);
        }
        declaration => panic!("expected inductive metadata, got {declaration:?}"),
    }
}

#[test]
fn universe_polymorphic_parameter_and_index_metadata_drive_inference() {
    let mut kernel = Kernel::new();
    let anon = kernel.anon();
    let box_name = kernel.name_str(anon, "UniverseBox");
    let ctor_name = kernel.name_str(box_name, "mk");
    let alpha_name = kernel.name_str(anon, "Alpha");
    let field_name = kernel.name_str(anon, "value");
    let u_name = kernel.name_str(anon, "u");
    let u = kernel.level_param(u_name);
    let sort_u = kernel.sort(u);
    let result_sort = {
        let succ_u = kernel.level_succ(u);
        kernel.sort(succ_u)
    };
    let alpha_fvar = 200;
    let field_fvar = 201;
    let alpha = kernel.fvar(alpha_fvar);
    let box_const = kernel.const_(box_name, vec![u]);
    let box_alpha = kernel.app(box_const, alpha);
    let ind_type = pi_telescope(
        &mut kernel,
        &[(alpha_fvar, alpha_name, sort_u)],
        result_sort,
    );
    let ctor_type = pi_telescope(
        &mut kernel,
        &[
            (alpha_fvar, alpha_name, sort_u),
            (field_fvar, field_name, alpha),
        ],
        box_alpha,
    );
    kernel
        .add_inductive(box_name, &[u_name], 1, ind_type, &[(ctor_name, ctor_type)])
        .unwrap();

    let zero = kernel.level_zero();
    let one = kernel.level_succ(zero);
    let prop = kernel.sort_zero();
    let instantiated_box = {
        let head = kernel.const_(box_name, vec![one]);
        kernel.app(head, prop)
    };
    let boxed_name = kernel.name_str(anon, "boxedProp");
    add_axiom(&mut kernel, boxed_name, instantiated_box);
    let boxed = kernel.const_(boxed_name, vec![]);
    let projection = kernel.proj(box_name, 0, boxed);
    assert_eq!(kernel.infer(projection).unwrap(), prop);

    let indexed_name = kernel.name_str(anon, "IndexedOne");
    let indexed_ctor = kernel.name_str(indexed_name, "mk");
    let index_name = kernel.name_str(anon, "index");
    let index_fvar = 300;
    let index = kernel.fvar(index_fvar);
    let indexed_const = kernel.const_(indexed_name, vec![]);
    let indexed_result = kernel.app(indexed_const, index);
    let indexed_result_sort = kernel.sort(one);
    let indexed_type = kernel.pi(index_name, prop, indexed_result_sort, BinderInfo::Default);
    let indexed_ctor_type = pi_telescope(
        &mut kernel,
        &[(index_fvar, index_name, prop)],
        indexed_result,
    );
    kernel
        .add_inductive(
            indexed_name,
            &[],
            0,
            indexed_type,
            &[(indexed_ctor, indexed_ctor_type)],
        )
        .unwrap();
    let proposition_name = kernel.name_str(anon, "P");
    add_axiom(&mut kernel, proposition_name, prop);
    let proposition = kernel.const_(proposition_name, vec![]);
    let indexed_at_p = {
        let head = kernel.const_(indexed_name, vec![]);
        kernel.app(head, proposition)
    };
    let indexed_value_name = kernel.name_str(anon, "indexedValue");
    add_axiom(&mut kernel, indexed_value_name, indexed_at_p);
    let indexed_value = kernel.const_(indexed_value_name, vec![]);
    let index_projection = kernel.proj(indexed_name, 0, indexed_value);
    assert_eq!(kernel.infer(index_projection).unwrap(), prop);
    match kernel.environment().get(indexed_name).unwrap() {
        Declaration::Inductive {
            num_params,
            num_indices,
            ..
        } => assert_eq!((*num_params, *num_indices), (0, 1)),
        declaration => panic!("expected indexed inductive, got {declaration:?}"),
    }
}

#[test]
fn wrong_name_index_shape_and_arity_reject_with_precise_errors() {
    let mut kernel = Kernel::new();
    let structure = add_dependent_structure(&mut kernel);
    let anon = kernel.anon();
    let prop = kernel.sort_zero();
    let predicate = {
        let body = kernel.bvar(0);
        kernel.lam(anon, prop, body, BinderInfo::Default)
    };
    let structure_type = {
        let head = kernel.const_(structure.name, vec![]);
        let at_prop = kernel.app(head, prop);
        kernel.app(at_prop, predicate)
    };
    let value_name = kernel.name_str(anon, "mutationValue");
    add_axiom(&mut kernel, value_name, structure_type);
    let value = kernel.const_(value_name, vec![]);

    let wrong_name = kernel.name_str(anon, "WrongStructureName");
    let wrong_name_projection = kernel.proj(wrong_name, 0, value);
    assert_eq!(
        kernel.infer(wrong_name_projection),
        Err(KernelError::ProjectionTypeMismatch {
            expected: wrong_name,
            got: structure_type,
        })
    );
    let out_of_range = kernel.proj(structure.name, 2, value);
    assert_eq!(
        kernel.infer(out_of_range),
        Err(KernelError::ProjectionFieldOutOfBounds {
            name: structure.name,
            field_index: 2,
            field_count: 2,
        })
    );

    let fake_name = kernel.name_str(anon, "NotAnInductive");
    add_axiom(&mut kernel, fake_name, prop);
    let fake_value_name = kernel.name_str(anon, "fakeValue");
    let fake_type = kernel.const_(fake_name, vec![]);
    add_axiom(&mut kernel, fake_value_name, fake_type);
    let fake_value = kernel.const_(fake_value_name, vec![]);
    let fake_projection = kernel.proj(fake_name, 0, fake_value);
    assert_eq!(
        kernel.infer(fake_projection),
        Err(KernelError::ProjectionNotInductive { name: fake_name })
    );

    let boolish = kernel.name_str(anon, "TwoConstructors");
    let left = kernel.name_str(boolish, "left");
    let right = kernel.name_str(boolish, "right");
    let sort_one = {
        let zero = kernel.level_zero();
        let one = kernel.level_succ(zero);
        kernel.sort(one)
    };
    let boolish_const = kernel.const_(boolish, vec![]);
    kernel
        .add_inductive(
            boolish,
            &[],
            0,
            sort_one,
            &[(left, boolish_const), (right, boolish_const)],
        )
        .unwrap();
    let boolish_value_name = kernel.name_str(anon, "twoCtorValue");
    add_axiom(&mut kernel, boolish_value_name, boolish_const);
    let boolish_value = kernel.const_(boolish_value_name, vec![]);
    let multi_projection = kernel.proj(boolish, 0, boolish_value);
    assert_eq!(
        kernel.infer(multi_projection),
        Err(KernelError::ProjectionConstructorCount {
            name: boolish,
            got: 2,
        })
    );

    let malformed_local = kernel.fvar(400);
    let malformed_type = kernel.const_(structure.name, vec![]);
    let malformed_projection = kernel.proj(structure.name, 0, malformed_local);
    let mut context = LocalContext::new();
    context.push(LocalDecl {
        fvar: 400,
        name: anon,
        ty: malformed_type,
        info: BinderInfo::Default,
    });
    assert_eq!(
        kernel.infer_in(malformed_projection, &mut context),
        Err(KernelError::ProjectionArityMismatch {
            name: structure.name,
            expected: 2,
            got: 0,
        })
    );
}

#[test]
fn prop_projection_rejects_data_elimination_but_allows_proof_fields() {
    let mut kernel = Kernel::new();
    let anon = kernel.anon();
    let prop = kernel.sort_zero();
    let sort_one = {
        let zero = kernel.level_zero();
        let one = kernel.level_succ(zero);
        kernel.sort(one)
    };

    let data_box = kernel.name_str(anon, "PropDataBox");
    let data_ctor = kernel.name_str(data_box, "mk");
    let data_name = kernel.name_str(anon, "data");
    let data_box_const = kernel.const_(data_box, vec![]);
    let data_ctor_type = kernel.pi(data_name, sort_one, data_box_const, BinderInfo::Default);
    kernel
        .add_inductive(data_box, &[], 0, prop, &[(data_ctor, data_ctor_type)])
        .unwrap();
    let data_value_name = kernel.name_str(anon, "propDataValue");
    let data_box_type = kernel.const_(data_box, vec![]);
    add_axiom(&mut kernel, data_value_name, data_box_type);
    let data_value = kernel.const_(data_value_name, vec![]);
    let forbidden = kernel.proj(data_box, 0, data_value);
    assert_eq!(
        kernel.infer(forbidden),
        Err(KernelError::ProjectionFromPropToType {
            name: data_box,
            field_index: 0,
        })
    );

    let proof_box = kernel.name_str(anon, "ProofBox");
    let proof_ctor = kernel.name_str(proof_box, "mk");
    let proposition_name = kernel.name_str(anon, "proposition");
    let proof_name = kernel.name_str(anon, "proof");
    let proposition_fvar = 500;
    let proof_fvar = 501;
    let proposition = kernel.fvar(proposition_fvar);
    let proof_box_const = kernel.const_(proof_box, vec![]);
    let proof_box_at_p = kernel.app(proof_box_const, proposition);
    let proof_box_type = pi_telescope(
        &mut kernel,
        &[(proposition_fvar, proposition_name, prop)],
        prop,
    );
    let proof_ctor_type = pi_telescope(
        &mut kernel,
        &[
            (proposition_fvar, proposition_name, prop),
            (proof_fvar, proof_name, proposition),
        ],
        proof_box_at_p,
    );
    kernel
        .add_inductive(
            proof_box,
            &[],
            1,
            proof_box_type,
            &[(proof_ctor, proof_ctor_type)],
        )
        .unwrap();
    let p_name = kernel.name_str(anon, "ProjectionProposition");
    add_axiom(&mut kernel, p_name, prop);
    let p = kernel.const_(p_name, vec![]);
    let proof_box_at_p = {
        let head = kernel.const_(proof_box, vec![]);
        kernel.app(head, p)
    };
    let proof_value_name = kernel.name_str(anon, "proofValue");
    add_axiom(&mut kernel, proof_value_name, proof_box_at_p);
    let proof_value = kernel.const_(proof_value_name, vec![]);
    let allowed = kernel.proj(proof_box, 0, proof_value);
    assert_eq!(kernel.infer(allowed).unwrap(), p);
}
