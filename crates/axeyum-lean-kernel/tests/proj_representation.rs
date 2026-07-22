//! TL2.2 representation and traversal gate for Lean core projections.
//!
//! This slice deliberately stops before projection inference and reduction.
//! The tests therefore cover the complete structural contract and require the
//! trusted admission boundary to reject an unbound projected child. TL2.3's
//! semantic inference contract has its own integration suite.

use axeyum_lean_kernel::{BinderInfo, Declaration, ExprNode, Kernel, KernelError};

fn projection_parts(
    k: &Kernel,
    expression: axeyum_lean_kernel::ExprId,
) -> (axeyum_lean_kernel::NameId, u32, axeyum_lean_kernel::ExprId) {
    let ExprNode::Proj(type_name, field_index, structure) = k.expr_node(expression) else {
        panic!("expected projection, got {:?}", k.expr_node(expression));
    };
    (*type_name, *field_index, *structure)
}

#[test]
fn projection_interning_metadata_and_payload_mutations_are_explicit() {
    let mut kernel = Kernel::new();
    let anon = kernel.anon();
    let pair = kernel.name_str(anon, "Pair");
    let other = kernel.name_str(anon, "Other");
    let function = kernel.bvar(2);
    let argument = kernel.fvar(41);
    let structure = kernel.app(function, argument);

    let projection = kernel.proj(pair, 1, structure);
    assert_eq!(projection, kernel.proj(pair, 1, structure));
    assert_ne!(projection, kernel.proj(other, 1, structure));
    assert_ne!(projection, kernel.proj(pair, 0, structure));
    let other_structure = kernel.fvar(42);
    assert_ne!(projection, kernel.proj(pair, 1, other_structure));
    assert_eq!(projection_parts(&kernel, projection), (pair, 1, structure));

    assert_eq!(kernel.num_loose_bvars(projection), 3);
    assert_eq!(kernel.loose_bvar_range(projection), 0..3);
    assert!(kernel.has_loose_bvars(projection));
    assert!(kernel.has_fvars(projection));
}

#[test]
fn projection_de_bruijn_and_level_operations_recurse_into_the_structure() {
    let mut kernel = Kernel::new();
    let anon = kernel.anon();
    let pair = kernel.name_str(anon, "Pair");
    let holder = kernel.name_str(anon, "Holder");
    let universe_name = kernel.name_str(anon, "u");
    let universe = kernel.level_param(universe_name);
    let holder_at_u = kernel.const_(holder, vec![universe]);
    let free = kernel.fvar(77);
    let loose = kernel.bvar(0);
    let open_tail = kernel.app(free, loose);
    let structure = kernel.app(holder_at_u, open_tail);
    let projection = kernel.proj(pair, 1, structure);

    let one = {
        let zero = kernel.level_zero();
        kernel.level_succ(zero)
    };
    let level_substituted = kernel.substitute_expr_levels(projection, &[(universe_name, one)]);
    let (sub_name, sub_index, substituted_structure) = projection_parts(&kernel, level_substituted);
    assert_eq!((sub_name, sub_index), (pair, 1));
    let ExprNode::App(substituted_holder, substituted_tail) =
        kernel.expr_node(substituted_structure)
    else {
        panic!("expected substituted structure application");
    };
    assert_eq!(*substituted_tail, open_tail);
    assert!(matches!(
        kernel.expr_node(*substituted_holder),
        ExprNode::Const(name, levels) if *name == holder && levels == &[one]
    ));

    let abstraction_source = kernel.proj(pair, 1, free);
    let abstracted = kernel.abstract_fvars(abstraction_source, &[77]);
    let (_, _, abstracted_structure) = projection_parts(&kernel, abstracted);
    assert!(matches!(
        kernel.expr_node(abstracted_structure),
        ExprNode::BVar(0)
    ));
    let replacement = kernel.fvar(77);
    assert_eq!(
        kernel.instantiate(abstracted, &[replacement]),
        abstraction_source
    );

    let lifted_base = kernel.bvar(1);
    let lifted_projection = kernel.proj(pair, 3, lifted_base);
    let lifted = kernel.lift_loose_bvars(lifted_projection, 1, 4);
    let (lifted_name, lifted_index, lifted_structure) = projection_parts(&kernel, lifted);
    assert_eq!((lifted_name, lifted_index), (pair, 3));
    assert!(matches!(
        kernel.expr_node(lifted_structure),
        ExprNode::BVar(5)
    ));
}

#[test]
fn scoped_free_variable_closure_descends_through_projection() {
    let mut kernel = Kernel::new();
    let anon = kernel.anon();
    let pair = kernel.name_str(anon, "Pair");
    let binder_name = kernel.name_str(anon, "self");
    let binder_type = kernel.sort_zero();
    let local = kernel.fvar(9001);
    let body = kernel.proj(pair, 0, local);
    let lambda = kernel.lam(binder_name, binder_type, body, BinderInfo::Default);

    let closed = kernel.close_scoped_fvars(lambda, &[(lambda, 9001)]);
    assert!(!kernel.has_fvars(closed));
    let ExprNode::Lam(_, _, closed_body, _) = kernel.expr_node(closed) else {
        panic!("expected closed lambda");
    };
    let (type_name, field_index, structure) = projection_parts(&kernel, *closed_body);
    assert_eq!((type_name, field_index), (pair, 0));
    assert!(matches!(kernel.expr_node(structure), ExprNode::BVar(0)));
}

#[test]
fn projection_is_neutral_and_child_inference_errors_remain_fail_closed() {
    let mut kernel = Kernel::new();
    let anon = kernel.anon();
    let pair = kernel.name_str(anon, "Pair");
    let structure = kernel.fvar(7);
    let projection = kernel.proj(pair, 0, structure);

    assert_eq!(kernel.whnf(projection), projection);
    assert_eq!(
        kernel.infer(projection),
        Err(KernelError::UnboundFVar { id: 7 })
    );
    assert!(kernel.def_eq(projection, projection));
    let other_structure = kernel.fvar(8);
    let other = kernel.proj(pair, 0, other_structure);
    assert!(!kernel.def_eq(projection, other));

    let bad_name = kernel.name_str(anon, "projectionCannotAdmitYet");
    let claimed_type = kernel.sort_zero();
    let error = kernel
        .add_declaration(Declaration::Definition {
            name: bad_name,
            uparams: vec![],
            ty: claimed_type,
            value: projection,
            hint: axeyum_lean_kernel::ReducibilityHint::Regular(0),
        })
        .unwrap_err();
    assert_eq!(error, KernelError::UnboundFVar { id: 7 });
    assert!(kernel.environment().get(bad_name).is_none());
}
