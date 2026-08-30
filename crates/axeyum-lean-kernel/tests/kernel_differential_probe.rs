//! Diagnostic probe for the ADR-0780 `inductives` mutant survivor.
//!
//! Not a gate. It prints the concrete `KernelError` each nearly-well-typed
//! inductive construction in `kernel_differential.rs` actually produces, so a
//! mutation can be aimed at the guard the case REACHES rather than the guard
//! its name suggests.

use axeyum_lean_kernel::{BinderInfo, Declaration, ExprId, Kernel};

fn arrow(kernel: &mut Kernel, domain: ExprId, codomain: ExprId) -> ExprId {
    let anon = kernel.anon();
    kernel.pi(anon, domain, codomain, BinderInfo::Default)
}

#[test]
fn probe_non_positive_occurrence_error() {
    // Exactly `inductives::non_positive_occurrence_negative`.
    let mut kernel = Kernel::new();
    let anon = kernel.anon();
    let zero_lvl = kernel.level_zero();
    let one_lvl = kernel.level_succ(zero_lvl);
    let bad = kernel.name_str(anon, "Bad");
    let bad_c = kernel.const_(bad, vec![]);
    let ty = kernel.sort(one_lvl);

    let cod_name = kernel.name_str(anon, "Codomain");
    let cod_ty = kernel.sort(one_lvl);
    kernel
        .add_declaration(Declaration::Axiom {
            name: cod_name,
            uparams: Vec::new(),
            ty: cod_ty,
        })
        .expect("Codomain axiom");
    let codomain = kernel.const_(cod_name, vec![]);

    let field_ty = arrow(&mut kernel, bad_c, codomain);
    let mk_ty = arrow(&mut kernel, field_ty, bad_c);
    let mk = kernel.name_str(bad, "mk");

    let result = kernel.add_inductive(bad, &[], 0, ty, &[(mk, mk_ty)]);
    println!("PROBE non_positive_occurrence_negative -> {result:?}");
}

#[test]
fn probe_constructor_result_mismatch_error() {
    let mut kernel = Kernel::new();
    let anon = kernel.anon();
    let zero_lvl = kernel.level_zero();
    let one_lvl = kernel.level_succ(zero_lvl);
    let two = kernel.name_str(anon, "TwoVals");
    let two_c = kernel.const_(two, vec![]);
    let sort_1 = kernel.sort(one_lvl);
    let ff = kernel.name_str(two, "ff");
    let tt = kernel.name_str(two, "tt");
    kernel
        .add_inductive(two, &[], 0, sort_1, &[(ff, two_c), (tt, two_c)])
        .expect("TwoVals must admit");

    let dom_name = kernel.name_str(anon, "Dom");
    let dom_ty = kernel.sort(one_lvl);
    kernel
        .add_declaration(Declaration::Axiom {
            name: dom_name,
            uparams: Vec::new(),
            ty: dom_ty,
        })
        .expect("Dom axiom");
    let domain = kernel.const_(dom_name, vec![]);

    let bad2 = kernel.name_str(anon, "Bad2");
    let mk_ty = arrow(&mut kernel, domain, two_c);
    let mk = kernel.name_str(bad2, "mk");
    let result = kernel.add_inductive(bad2, &[], 0, sort_1, &[(mk, mk_ty)]);
    println!("PROBE constructor_result_mismatch_negative -> {result:?}");
}
