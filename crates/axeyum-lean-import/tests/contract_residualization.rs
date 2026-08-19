//! Controls for ADR-0489's checked contract-body residualization.

#[path = "../examples/statement_reflexivity_support/mod.rs"]
mod support;

use axeyum_lean_import::{
    ConstantInstance, ResidualizedFunctionContractError, residualize_function_contract_body,
};
use axeyum_lean_kernel::{
    BinderInfo, Declaration, Kernel, LogicPrelude, NameId, ReducibilityHint, build_logic_prelude,
};

fn name(kernel: &mut Kernel, parts: &[&str]) -> NameId {
    let mut result = kernel.anon();
    for part in parts {
        result = kernel.name_str(result, *part);
    }
    result
}

fn instance(kernel: &mut Kernel, source: NameId, binder: &str) -> ConstantInstance {
    ConstantInstance {
        name: source,
        levels: vec![],
        binder_name: name(kernel, &[binder]),
    }
}

struct Fixture {
    kernel: Kernel,
    logic: LogicPrelude,
    source: NameId,
    helper: NameId,
}

fn fixture() -> Fixture {
    let mut kernel = Kernel::new();
    let logic = build_logic_prelude(&mut kernel).expect("logic prelude builds");
    let anonymous = kernel.anon();
    let nat = kernel.const_(logic.nat, vec![]);
    let function_type = kernel.pi(anonymous, nat, nat, BinderInfo::Default);
    let helper = name(&mut kernel, &["Source", "helper"]);
    let helper_body = kernel.bvar(0);
    let helper_value = kernel.lam(anonymous, nat, helper_body, BinderInfo::Default);
    kernel
        .add_declaration(Declaration::Definition {
            name: helper,
            uparams: vec![],
            ty: function_type,
            value: helper_value,
            hint: ReducibilityHint::Regular(0),
        })
        .expect("helper definition checks");
    let source = name(&mut kernel, &["Source", "function"]);
    let helper_term = kernel.const_(helper, vec![]);
    let argument = kernel.bvar(0);
    let source_body = kernel.app(helper_term, argument);
    let source_value = kernel.lam(anonymous, nat, source_body, BinderInfo::Default);
    kernel
        .add_declaration(Declaration::Definition {
            name: source,
            uparams: vec![],
            ty: function_type,
            value: source_value,
            hint: ReducibilityHint::Regular(0),
        })
        .expect("source definition checks");
    Fixture {
        kernel,
        logic,
        source,
        helper,
    }
}

#[test]
fn omitted_helper_becomes_an_ordered_parameter_and_specializes_exactly() {
    let mut fixture = fixture();
    let source = instance(&mut fixture.kernel, fixture.source, "f");
    let helper = instance(&mut fixture.kernel, fixture.helper, "helper");
    let nat = instance(&mut fixture.kernel, fixture.logic.nat, "Nat");
    let contract =
        residualize_function_contract_body(&mut fixture.kernel, &source, &[helper], &[nat])
            .expect("one omitted helper must residualize");
    assert_eq!(contract.function_arity, 1);
    assert_eq!(contract.generalized.binders.len(), 2);
    assert_eq!(contract.source_arguments.len(), 2);
    assert!(!fixture.kernel.has_fvars(contract.generalized.goal));
    assert!(!fixture.kernel.has_loose_bvars(contract.generalized.goal));
    let witness = support::propose_reflexivity(&mut fixture.kernel, contract.source_equation)
        .expect("the exact source equation has a bounded reflexivity witness");
    let witness_name = name(&mut fixture.kernel, &["Generated", "residualized_witness"]);
    fixture
        .kernel
        .add_declaration(Declaration::Theorem {
            name: witness_name,
            uparams: vec![],
            ty: contract.source_equation,
            value: witness.proof,
        })
        .expect("source kernel accepts the residualized equation witness");
    assert_eq!(witness.binders, 1);
    assert_eq!(witness.constructed_nodes, 4);
    assert!(fixture.kernel.axiom_footprint(witness_name).is_empty());
    assert!(fixture.kernel.theorem_dependencies(witness_name).is_empty());
}

#[test]
fn omission_and_duplicate_authority_fail_closed() {
    let mut fixture = fixture();
    let source = instance(&mut fixture.kernel, fixture.source, "f");
    let helper = instance(&mut fixture.kernel, fixture.helper, "helper");
    let nat = instance(&mut fixture.kernel, fixture.logic.nat, "Nat");
    assert!(matches!(
        residualize_function_contract_body(
            &mut fixture.kernel,
            &source,
            &[],
            std::slice::from_ref(&nat),
        ),
        Err(ResidualizedFunctionContractError::UnaccountedBodyConstant { .. })
    ));
    let duplicate_retained = vec![nat, helper.clone()];
    assert!(matches!(
        residualize_function_contract_body(
            &mut fixture.kernel,
            &source,
            std::slice::from_ref(&helper),
            &duplicate_retained,
        ),
        Err(ResidualizedFunctionContractError::DuplicateAuthority { .. })
    ));
}

#[test]
fn dependency_order_is_checked_by_the_existing_generalizer() {
    let mut kernel = Kernel::new();
    let logic = build_logic_prelude(&mut kernel).expect("logic prelude builds");
    let anonymous = kernel.anon();
    let zero = kernel.level_zero();
    let one = kernel.level_succ(zero);
    let sort_one = kernel.sort(one);
    let carrier = name(&mut kernel, &["Source", "Carrier"]);
    let nat = kernel.const_(logic.nat, vec![]);
    kernel
        .add_declaration(Declaration::Definition {
            name: carrier,
            uparams: vec![],
            ty: sort_one,
            value: nat,
            hint: ReducibilityHint::Regular(0),
        })
        .expect("carrier alias checks");
    let carrier_type = kernel.const_(carrier, vec![]);
    let value = name(&mut kernel, &["Source", "value"]);
    let nat_zero = kernel.const_(logic.nat_zero, vec![]);
    kernel
        .add_declaration(Declaration::Definition {
            name: value,
            uparams: vec![],
            ty: carrier_type,
            value: nat_zero,
            hint: ReducibilityHint::Regular(0),
        })
        .expect("dependent value checks");
    let source = name(&mut kernel, &["Source", "constant"]);
    let function_type = kernel.pi(anonymous, nat, carrier_type, BinderInfo::Default);
    let value_term = kernel.const_(value, vec![]);
    let source_value = kernel.lam(anonymous, nat, value_term, BinderInfo::Default);
    kernel
        .add_declaration(Declaration::Definition {
            name: source,
            uparams: vec![],
            ty: function_type,
            value: source_value,
            hint: ReducibilityHint::Regular(0),
        })
        .expect("constant function checks");
    let source = instance(&mut kernel, source, "f");
    let value = instance(&mut kernel, value, "value");
    let carrier = instance(&mut kernel, carrier, "Carrier");
    let nat_type = instance(&mut kernel, logic.nat, "Nat");
    assert!(matches!(
        residualize_function_contract_body(&mut kernel, &source, &[value, carrier], &[nat_type],),
        Err(ResidualizedFunctionContractError::Slice(_))
    ));
}
