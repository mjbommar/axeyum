//! Controls for ADR-0491's trace-backed source-contract receipt.

use axeyum_lean_import::{
    ConstantInstance, TraceBackedSourceContractReceiptError,
    issue_trace_backed_source_contract_receipt, verify_trace_backed_source_contract_receipt,
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
    let helper = name(&mut kernel, &["Receipt", "helper"]);
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
        .expect("helper checks");
    let source = name(&mut kernel, &["Receipt", "source"]);
    let helper_term = kernel.const_(helper, vec![]);
    let argument = kernel.bvar(0);
    let body = kernel.app(helper_term, argument);
    let value = kernel.lam(anonymous, nat, body, BinderInfo::Default);
    kernel
        .add_declaration(Declaration::Definition {
            name: source,
            uparams: vec![],
            ty: function_type,
            value,
            hint: ReducibilityHint::Regular(1),
        })
        .expect("source checks");
    Fixture {
        kernel,
        logic,
        source,
        helper,
    }
}

#[test]
fn exact_contract_trace_issues_and_replays_without_a_witness_theorem() {
    let mut fixture = fixture();
    let source = instance(&mut fixture.kernel, fixture.source, "sourceFn");
    let residual = instance(&mut fixture.kernel, fixture.helper, "helperFn");
    let retained = instance(&mut fixture.kernel, fixture.logic.nat, "Nat");
    let receipt = issue_trace_backed_source_contract_receipt(
        &mut fixture.kernel,
        &source,
        std::slice::from_ref(&residual),
        std::slice::from_ref(&retained),
        "synthetic-trace-backed-contract-v1",
    )
    .expect("exact trace-backed contract issues");
    assert!(receipt.has_valid_digest());
    assert_eq!(receipt.function_arity, 1);
    assert_eq!(receipt.contract_binders, 2);
    assert_eq!(receipt.consulted_declarations, ["Receipt.source"]);
    assert!(receipt.source_axiom_footprint.is_empty());
    assert_eq!(receipt.source.role, "source");
    assert_eq!(receipt.residual[0].role, "residual");
    assert_eq!(receipt.retained[0].role, "retained");
    assert!(receipt.to_pretty_json().unwrap().ends_with('\n'));
    verify_trace_backed_source_contract_receipt(
        &receipt,
        &mut fixture.kernel,
        &source,
        std::slice::from_ref(&residual),
        std::slice::from_ref(&retained),
    )
    .expect("receipt reissues exactly");

    for mutate in [
        |receipt: &mut axeyum_lean_import::TraceBackedSourceContractReceipt| {
            receipt.source.content_sha256 = "mutated".to_owned();
        },
        |receipt: &mut axeyum_lean_import::TraceBackedSourceContractReceipt| {
            receipt.generalized_contract_sha256 = "mutated".to_owned();
        },
        |receipt: &mut axeyum_lean_import::TraceBackedSourceContractReceipt| {
            receipt.delta_after_sha256 = "mutated".to_owned();
        },
        |receipt: &mut axeyum_lean_import::TraceBackedSourceContractReceipt| {
            receipt
                .consulted_declarations
                .push("Receipt.helper".to_owned());
        },
    ] {
        let mut mutated = receipt.clone();
        mutate(&mut mutated);
        assert_eq!(
            verify_trace_backed_source_contract_receipt(
                &mutated,
                &mut fixture.kernel,
                &source,
                std::slice::from_ref(&residual),
                std::slice::from_ref(&retained),
            ),
            Err(TraceBackedSourceContractReceiptError::ReceiptMismatch)
        );
    }

    let renamed_source = instance(&mut fixture.kernel, fixture.source, "renamedSource");
    assert_eq!(
        verify_trace_backed_source_contract_receipt(
            &receipt,
            &mut fixture.kernel,
            &renamed_source,
            std::slice::from_ref(&residual),
            std::slice::from_ref(&retained),
        ),
        Err(TraceBackedSourceContractReceiptError::ReceiptMismatch)
    );
}

#[test]
fn omitted_residual_and_trusted_direct_instance_fail_closed() {
    let mut fixture = fixture();
    let source = instance(&mut fixture.kernel, fixture.source, "sourceFn");
    let retained = instance(&mut fixture.kernel, fixture.logic.nat, "Nat");
    assert!(matches!(
        issue_trace_backed_source_contract_receipt(
            &mut fixture.kernel,
            &source,
            &[],
            std::slice::from_ref(&retained),
            "synthetic-trace-backed-contract-v1",
        ),
        Err(TraceBackedSourceContractReceiptError::Contract(_))
    ));

    let trusted = name(&mut fixture.kernel, &["Upstream", "trustedData"]);
    let nat = fixture.kernel.const_(fixture.logic.nat, vec![]);
    fixture
        .kernel
        .add_declaration(Declaration::Axiom {
            name: trusted,
            uparams: vec![],
            ty: nat,
        })
        .expect("trusted data control checks");
    let trusted = instance(&mut fixture.kernel, trusted, "trustedData");
    assert!(matches!(
        issue_trace_backed_source_contract_receipt(
            &mut fixture.kernel,
            &source,
            &[],
            &[retained, trusted],
            "synthetic-trace-backed-contract-v1",
        ),
        Err(TraceBackedSourceContractReceiptError::TrustedDirectInstance { kind: "axiom", .. })
    ));
}

#[test]
fn axiom_hidden_below_a_residual_definition_is_rejected() {
    let mut fixture = fixture();
    let anonymous = fixture.kernel.anon();
    let nat = fixture.kernel.const_(fixture.logic.nat, vec![]);
    let function_type = fixture.kernel.pi(anonymous, nat, nat, BinderInfo::Default);
    let answer = name(&mut fixture.kernel, &["Upstream", "hiddenAnswer"]);
    fixture
        .kernel
        .add_declaration(Declaration::Axiom {
            name: answer,
            uparams: vec![],
            ty: nat,
        })
        .expect("hidden answer control checks");
    let helper = name(&mut fixture.kernel, &["Contaminated", "helper"]);
    let answer_term = fixture.kernel.const_(answer, vec![]);
    let helper_value = fixture
        .kernel
        .lam(anonymous, nat, answer_term, BinderInfo::Default);
    fixture
        .kernel
        .add_declaration(Declaration::Definition {
            name: helper,
            uparams: vec![],
            ty: function_type,
            value: helper_value,
            hint: ReducibilityHint::Regular(0),
        })
        .expect("contaminated helper checks");
    let source_name = name(&mut fixture.kernel, &["Contaminated", "source"]);
    let helper_term = fixture.kernel.const_(helper, vec![]);
    let argument = fixture.kernel.bvar(0);
    let source_body = fixture.kernel.app(helper_term, argument);
    let source_value = fixture
        .kernel
        .lam(anonymous, nat, source_body, BinderInfo::Default);
    fixture
        .kernel
        .add_declaration(Declaration::Definition {
            name: source_name,
            uparams: vec![],
            ty: function_type,
            value: source_value,
            hint: ReducibilityHint::Regular(1),
        })
        .expect("contaminated source checks");
    let source = instance(&mut fixture.kernel, source_name, "sourceFn");
    let residual = instance(&mut fixture.kernel, helper, "helperFn");
    let retained = instance(&mut fixture.kernel, fixture.logic.nat, "Nat");
    assert_eq!(
        issue_trace_backed_source_contract_receipt(
            &mut fixture.kernel,
            &source,
            std::slice::from_ref(&residual),
            std::slice::from_ref(&retained),
            "synthetic-trace-backed-contract-v1",
        ),
        Err(
            TraceBackedSourceContractReceiptError::SourceAxiomFootprint {
                names: vec!["Upstream.hiddenAnswer".to_owned()],
            }
        )
    );
}
