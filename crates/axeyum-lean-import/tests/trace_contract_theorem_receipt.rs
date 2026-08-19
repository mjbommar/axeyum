//! Adversarial controls for ADR-0493's contract-to-theorem receipt bridge.

use axeyum_lean_import::{
    ConstantInstance, TraceBackedSemanticTheoremReceiptError,
    issue_trace_backed_semantic_theorem_receipt, issue_trace_backed_source_contract_receipt,
    verify_trace_backed_semantic_theorem_receipt,
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
    let inner = kernel.pi(anonymous, nat, nat, BinderInfo::Default);
    let function_type = kernel.pi(anonymous, nat, inner, BinderInfo::Default);
    let helper = name(&mut kernel, &["Bridge", "helper"]);
    let x = kernel.bvar(1);
    let helper_inner = kernel.lam(anonymous, nat, x, BinderInfo::Default);
    let helper_value = kernel.lam(anonymous, nat, helper_inner, BinderInfo::Default);
    kernel
        .add_declaration(Declaration::Definition {
            name: helper,
            uparams: vec![],
            ty: function_type,
            value: helper_value,
            hint: ReducibilityHint::Regular(0),
        })
        .expect("helper checks");
    let source = name(&mut kernel, &["Bridge", "source"]);
    let helper_term = kernel.const_(helper, vec![]);
    let x = kernel.bvar(1);
    let y = kernel.bvar(0);
    let applied = kernel.app(helper_term, x);
    let applied = kernel.app(applied, y);
    let source_inner = kernel.lam(anonymous, nat, applied, BinderInfo::Default);
    let source_value = kernel.lam(anonymous, nat, source_inner, BinderInfo::Default);
    kernel
        .add_declaration(Declaration::Definition {
            name: source,
            uparams: vec![],
            ty: function_type,
            value: source_value,
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

fn authority(fixture: &mut Fixture) -> (ConstantInstance, ConstantInstance, ConstantInstance) {
    let source = instance(&mut fixture.kernel, fixture.source, "sourceFn");
    let residual = instance(&mut fixture.kernel, fixture.helper, "helperFn");
    let retained = instance(&mut fixture.kernel, fixture.logic.nat, "Nat");
    (source, residual, retained)
}

#[test]
fn exact_source_receipt_issues_one_bounded_axiom_free_theorem_receipt() {
    let mut fixture = fixture();
    let (source, residual, retained) = authority(&mut fixture);
    let source_receipt = issue_trace_backed_source_contract_receipt(
        &mut fixture.kernel,
        &source,
        std::slice::from_ref(&residual),
        std::slice::from_ref(&retained),
        "synthetic-source-contract-v1",
    )
    .expect("source receipt issues");
    let theorem = name(&mut fixture.kernel, &["Axeyum", "Autogenesis", "Bridge"]);
    let receipt = issue_trace_backed_semantic_theorem_receipt(
        &mut fixture.kernel,
        &source_receipt,
        &source,
        std::slice::from_ref(&residual),
        std::slice::from_ref(&retained),
        theorem,
        "synthetic-contract-theorem-v1",
    )
    .expect("semantic theorem receipt issues");
    assert!(receipt.has_valid_digest());
    assert_eq!(receipt.operation, "trace-contract-reflexivity-v1");
    assert_eq!(receipt.binders, 2);
    assert_eq!(receipt.constructed_nodes, 5);
    assert!(receipt.axiom_footprint.is_empty());
    assert_eq!(
        receipt.source_equation_sha256,
        source_receipt.source_equation_sha256
    );
    assert!(receipt.to_pretty_json().unwrap().ends_with('\n'));
    verify_trace_backed_semantic_theorem_receipt(
        &receipt,
        &mut fixture.kernel,
        &source_receipt,
        &source,
        std::slice::from_ref(&residual),
        std::slice::from_ref(&retained),
        theorem,
    )
    .expect("semantic theorem receipt replays");
}

#[test]
fn mutations_and_wrong_authority_fail_closed() {
    let mut fixture = fixture();
    let (source, residual, retained) = authority(&mut fixture);
    let source_receipt = issue_trace_backed_source_contract_receipt(
        &mut fixture.kernel,
        &source,
        std::slice::from_ref(&residual),
        std::slice::from_ref(&retained),
        "synthetic-source-contract-v1",
    )
    .expect("source receipt issues");
    let theorem = name(&mut fixture.kernel, &["Axeyum", "Autogenesis", "Bridge"]);
    let receipt = issue_trace_backed_semantic_theorem_receipt(
        &mut fixture.kernel,
        &source_receipt,
        &source,
        std::slice::from_ref(&residual),
        std::slice::from_ref(&retained),
        theorem,
        "synthetic-contract-theorem-v1",
    )
    .expect("semantic theorem receipt issues");

    let mut mutated = receipt.clone();
    mutated.proof_sha256 = "mutated".to_owned();
    assert_eq!(
        verify_trace_backed_semantic_theorem_receipt(
            &mutated,
            &mut fixture.kernel,
            &source_receipt,
            &source,
            std::slice::from_ref(&residual),
            std::slice::from_ref(&retained),
            theorem,
        ),
        Err(TraceBackedSemanticTheoremReceiptError::ReceiptMismatch)
    );

    let mut stale_source_receipt = source_receipt.clone();
    stale_source_receipt.delta_after_sha256 = "mutated".to_owned();
    assert!(matches!(
        verify_trace_backed_semantic_theorem_receipt(
            &receipt,
            &mut fixture.kernel,
            &stale_source_receipt,
            &source,
            std::slice::from_ref(&residual),
            std::slice::from_ref(&retained),
            theorem,
        ),
        Err(TraceBackedSemanticTheoremReceiptError::SourceReceipt(_))
    ));
}

#[test]
fn issue_is_single_use_and_policy_is_required() {
    let mut fixture = fixture();
    let (source, residual, retained) = authority(&mut fixture);
    let source_receipt = issue_trace_backed_source_contract_receipt(
        &mut fixture.kernel,
        &source,
        std::slice::from_ref(&residual),
        std::slice::from_ref(&retained),
        "synthetic-source-contract-v1",
    )
    .expect("source receipt issues");
    let theorem = name(&mut fixture.kernel, &["Axeyum", "Autogenesis", "Bridge"]);
    assert_eq!(
        issue_trace_backed_semantic_theorem_receipt(
            &mut fixture.kernel,
            &source_receipt,
            &source,
            std::slice::from_ref(&residual),
            std::slice::from_ref(&retained),
            theorem,
            "",
        ),
        Err(TraceBackedSemanticTheoremReceiptError::EmptyPolicy)
    );
    issue_trace_backed_semantic_theorem_receipt(
        &mut fixture.kernel,
        &source_receipt,
        &source,
        std::slice::from_ref(&residual),
        std::slice::from_ref(&retained),
        theorem,
        "synthetic-contract-theorem-v1",
    )
    .expect("first issue succeeds");
    assert_eq!(
        issue_trace_backed_semantic_theorem_receipt(
            &mut fixture.kernel,
            &source_receipt,
            &source,
            std::slice::from_ref(&residual),
            std::slice::from_ref(&retained),
            theorem,
            "synthetic-contract-theorem-v1",
        ),
        Err(TraceBackedSemanticTheoremReceiptError::TargetExists)
    );
}
