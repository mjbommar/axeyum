//! TL2.4 gate for constructor projection reduction.
//!
//! Structure eta and wire import remain separate TL2.5/K1 gates.

use axeyum_lean_kernel::{
    BinderInfo, Declaration, ExprId, Kernel, KernelError, NameId, ReducibilityHint,
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

struct UniversePair {
    name: NameId,
    ctor: NameId,
    u_name: NameId,
}

fn add_universe_pair(kernel: &mut Kernel) -> UniversePair {
    let anon = kernel.anon();
    let name = kernel.name_str(anon, "UniversePair");
    let ctor = kernel.name_str(name, "mk");
    let u_name = kernel.name_str(anon, "u");
    let alpha_name = kernel.name_str(anon, "Alpha");
    let left_name = kernel.name_str(anon, "left");
    let transform_name = kernel.name_str(anon, "transform");
    let u = kernel.level_param(u_name);
    let sort_u = kernel.sort(u);
    let result_sort = {
        let succ_u = kernel.level_succ(u);
        kernel.sort(succ_u)
    };
    let alpha_fvar = 10;
    let left_fvar = 11;
    let transform_fvar = 12;
    let alpha = kernel.fvar(alpha_fvar);
    let transform_type = kernel.pi(anon, alpha, alpha, BinderInfo::Default);
    let ind_type = pi_telescope(kernel, &[(alpha_fvar, alpha_name, sort_u)], result_sort);
    let result = {
        let head = kernel.const_(name, vec![u]);
        kernel.app(head, alpha)
    };
    let ctor_type = pi_telescope(
        kernel,
        &[
            (alpha_fvar, alpha_name, sort_u),
            (left_fvar, left_name, alpha),
            (transform_fvar, transform_name, transform_type),
        ],
        result,
    );
    kernel
        .add_inductive(name, &[u_name], 1, ind_type, &[(ctor, ctor_type)])
        .expect("universe-polymorphic structure should admit");
    UniversePair { name, ctor, u_name }
}

#[test]
fn parameterized_universe_projection_skips_params_and_reapplies_outer_spine() {
    let mut kernel = Kernel::new();
    let pair = add_universe_pair(&mut kernel);
    let anon = kernel.anon();
    let proposition_name = kernel.name_str(anon, "P");
    let identity_name = kernel.name_str(anon, "identity");
    let prop = kernel.sort_zero();
    add_axiom(&mut kernel, proposition_name, prop);
    let proposition = kernel.const_(proposition_name, vec![]);
    let identity = {
        let body = kernel.bvar(0);
        kernel.lam(identity_name, prop, body, BinderInfo::Default)
    };
    let one = {
        let zero = kernel.level_zero();
        kernel.level_succ(zero)
    };
    let value = {
        let ctor = kernel.const_(pair.ctor, vec![one]);
        let with_param = kernel.app(ctor, prop);
        let with_left = kernel.app(with_param, proposition);
        kernel.app(with_left, identity)
    };

    let left = kernel.proj(pair.name, 0, value);
    assert_eq!(kernel.whnf(left), proposition);
    assert_eq!(kernel.infer(left).unwrap(), prop);

    let transform = kernel.proj(pair.name, 1, value);
    let applied_transform = kernel.app(transform, proposition);
    assert_eq!(kernel.whnf(applied_transform), proposition);

    match kernel.environment().get(pair.name).unwrap() {
        Declaration::Inductive {
            uparams,
            num_params,
            num_indices,
            ..
        } => {
            assert_eq!(uparams, &[pair.u_name]);
            assert_eq!((*num_params, *num_indices), (1, 0));
        }
        declaration => panic!("expected inductive metadata, got {declaration:?}"),
    }
}

#[test]
fn dependent_second_projection_reduces_to_its_proof_field() {
    let mut kernel = Kernel::new();
    let anon = kernel.anon();
    let structure_name = kernel.name_str(anon, "DependentPairReduction");
    let ctor_name = kernel.name_str(structure_name, "mk");
    let alpha_name = kernel.name_str(anon, "Alpha");
    let predicate_name = kernel.name_str(anon, "predicate");
    let first_name = kernel.name_str(anon, "first");
    let second_name = kernel.name_str(anon, "second");
    let proposition_name = kernel.name_str(anon, "P");
    let proof_name = kernel.name_str(anon, "pProof");
    let prop = kernel.sort_zero();
    let sort_one = {
        let zero = kernel.level_zero();
        let one = kernel.level_succ(zero);
        kernel.sort(one)
    };

    let alpha_fvar = 20;
    let predicate_fvar = 21;
    let first_fvar = 22;
    let second_fvar = 23;
    let alpha = kernel.fvar(alpha_fvar);
    let predicate = kernel.fvar(predicate_fvar);
    let first = kernel.fvar(first_fvar);
    let predicate_type = kernel.pi(anon, alpha, prop, BinderInfo::Default);
    let ind_type = pi_telescope(
        &mut kernel,
        &[
            (alpha_fvar, alpha_name, sort_one),
            (predicate_fvar, predicate_name, predicate_type),
        ],
        sort_one,
    );
    let result = {
        let head = kernel.const_(structure_name, vec![]);
        let with_alpha = kernel.app(head, alpha);
        kernel.app(with_alpha, predicate)
    };
    let second_type = kernel.app(predicate, first);
    let ctor_type = pi_telescope(
        &mut kernel,
        &[
            (alpha_fvar, alpha_name, sort_one),
            (predicate_fvar, predicate_name, predicate_type),
            (first_fvar, first_name, alpha),
            (second_fvar, second_name, second_type),
        ],
        result,
    );
    kernel
        .add_inductive(structure_name, &[], 2, ind_type, &[(ctor_name, ctor_type)])
        .unwrap();

    add_axiom(&mut kernel, proposition_name, prop);
    let proposition = kernel.const_(proposition_name, vec![]);
    add_axiom(&mut kernel, proof_name, proposition);
    let proof = kernel.const_(proof_name, vec![]);
    let predicate_value = {
        let body = kernel.bvar(0);
        kernel.lam(predicate_name, prop, body, BinderInfo::Default)
    };
    let value = {
        let ctor = kernel.const_(ctor_name, vec![]);
        let with_alpha = kernel.app(ctor, prop);
        let with_predicate = kernel.app(with_alpha, predicate_value);
        let with_first = kernel.app(with_predicate, proposition);
        kernel.app(with_first, proof)
    };
    let first_projection = kernel.proj(structure_name, 0, value);
    let second_projection = kernel.proj(structure_name, 1, value);

    assert_eq!(kernel.whnf(first_projection), proposition);
    assert_eq!(kernel.whnf(second_projection), proof);
    let inferred_second = kernel.infer(second_projection).unwrap();
    assert!(kernel.def_eq(inferred_second, proposition));
}

#[test]
fn projection_reduces_through_definitions_but_not_opaque_or_neutral_values() {
    let mut kernel = Kernel::new();
    let pair = add_universe_pair(&mut kernel);
    let anon = kernel.anon();
    let proposition_name = kernel.name_str(anon, "DefinitionP");
    let definition_name = kernel.name_str(anon, "definedPair");
    let opaque_name = kernel.name_str(anon, "opaquePair");
    let neutral_name = kernel.name_str(anon, "neutralPair");
    let identity_name = kernel.name_str(anon, "definitionIdentity");
    let prop = kernel.sort_zero();
    add_axiom(&mut kernel, proposition_name, prop);
    let proposition = kernel.const_(proposition_name, vec![]);
    let identity = {
        let body = kernel.bvar(0);
        kernel.lam(identity_name, prop, body, BinderInfo::Default)
    };
    let one = {
        let zero = kernel.level_zero();
        kernel.level_succ(zero)
    };
    let pair_type = {
        let head = kernel.const_(pair.name, vec![one]);
        kernel.app(head, prop)
    };
    let value = {
        let ctor = kernel.const_(pair.ctor, vec![one]);
        let with_param = kernel.app(ctor, prop);
        let with_left = kernel.app(with_param, proposition);
        kernel.app(with_left, identity)
    };
    kernel
        .add_declaration(Declaration::Definition {
            name: definition_name,
            uparams: vec![],
            ty: pair_type,
            value,
            hint: ReducibilityHint::Regular(0),
        })
        .unwrap();
    kernel
        .add_declaration(Declaration::Opaque {
            name: opaque_name,
            uparams: vec![],
            ty: pair_type,
            value,
        })
        .unwrap();
    add_axiom(&mut kernel, neutral_name, pair_type);

    let defined = kernel.const_(definition_name, vec![]);
    let defined_projection = kernel.proj(pair.name, 0, defined);
    assert_eq!(kernel.whnf(defined_projection), proposition);

    for name in [opaque_name, neutral_name] {
        let neutral = kernel.const_(name, vec![]);
        let projection = kernel.proj(pair.name, 0, neutral);
        assert_eq!(kernel.whnf(projection), projection);
    }

    let partial_ctor = {
        let ctor = kernel.const_(pair.ctor, vec![one]);
        kernel.app(ctor, prop)
    };
    let missing_field = kernel.proj(pair.name, 0, partial_ctor);
    assert_eq!(kernel.whnf(missing_field), missing_field);

    // `reduce_proj_core` is a computation rule, not a type checker: once the
    // requested checked field is present, a later ill-typed argument does not
    // change which constructor payload is selected. Inference remains the gate
    // that rejects ill-typed projection terms.
    let over_applied = kernel.app(value, proposition);
    let first_of_over_applied = kernel.proj(pair.name, 0, over_applied);
    assert_eq!(kernel.whnf(first_of_over_applied), proposition);
}

#[test]
fn reduction_follows_constructor_but_inference_still_rejects_wrong_structure_name() {
    let mut kernel = Kernel::new();
    let pair = add_universe_pair(&mut kernel);
    let anon = kernel.anon();
    let proposition_name = kernel.name_str(anon, "WrongNameP");
    let wrong_name = kernel.name_str(anon, "WrongStructureName");
    let identity_name = kernel.name_str(anon, "wrongNameIdentity");
    let prop = kernel.sort_zero();
    add_axiom(&mut kernel, proposition_name, prop);
    let proposition = kernel.const_(proposition_name, vec![]);
    let identity = {
        let body = kernel.bvar(0);
        kernel.lam(identity_name, prop, body, BinderInfo::Default)
    };
    let one = {
        let zero = kernel.level_zero();
        kernel.level_succ(zero)
    };
    let value = {
        let ctor = kernel.const_(pair.ctor, vec![one]);
        let with_param = kernel.app(ctor, prop);
        let with_left = kernel.app(with_param, proposition);
        kernel.app(with_left, identity)
    };
    let wrong_projection = kernel.proj(wrong_name, 0, value);

    // Lean's reducer selects from the actual constructor; the structure-name
    // well-typedness check belongs to inference and still rejects this term.
    assert_eq!(kernel.whnf(wrong_projection), proposition);
    let error = kernel.infer(wrong_projection).unwrap_err();
    assert!(matches!(
        error,
        KernelError::ProjectionTypeMismatch {
            expected,
            ..
        } if expected == wrong_name
    ));
}
