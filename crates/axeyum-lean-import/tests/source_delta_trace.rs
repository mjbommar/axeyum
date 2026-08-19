//! Controls for ADR-0490's bounded one-source delta trace.

use axeyum_lean_import::{SourceDeltaStepError, build_source_delta_step, verify_source_delta_step};
use axeyum_lean_kernel::{
    BinderInfo, Declaration, ExprNode, Kernel, LogicPrelude, NameId, ReducibilityHint,
    build_logic_prelude,
};

fn name(kernel: &mut Kernel, parts: &[&str]) -> NameId {
    let mut result = kernel.anon();
    for part in parts {
        result = kernel.name_str(result, *part);
    }
    result
}

struct Fixture {
    kernel: Kernel,
    logic: LogicPrelude,
    source: NameId,
    helper: NameId,
    source_value: axeyum_lean_kernel::ExprId,
}

fn fixture() -> Fixture {
    let mut kernel = Kernel::new();
    let logic = build_logic_prelude(&mut kernel).expect("logic prelude builds");
    let anonymous = kernel.anon();
    let nat = kernel.const_(logic.nat, vec![]);
    let function_type = kernel.pi(anonymous, nat, nat, BinderInfo::Default);
    let helper = name(&mut kernel, &["Trace", "helper"]);
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
    let source = name(&mut kernel, &["Trace", "source"]);
    let helper_term = kernel.const_(helper, vec![]);
    let source_argument = kernel.bvar(0);
    let source_body = kernel.app(helper_term, source_argument);
    let source_value = kernel.lam(anonymous, nat, source_body, BinderInfo::Default);
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
        source_value,
    }
}

#[test]
fn exact_source_unfold_is_checked_without_opening_the_helper() {
    let mut fixture = fixture();
    let trace = build_source_delta_step(&mut fixture.kernel, fixture.source, &[], &[])
        .expect("one exact source delta step checks");
    assert_eq!(trace.after, fixture.source_value);
    assert!(trace.arguments.is_empty());
    assert_eq!(trace.source, fixture.source);
    assert_eq!(trace.source_content_sha256.len(), 64);
    let ExprNode::Lam(_, _, body, _) = fixture.kernel.expr_node(trace.after) else {
        panic!("the one-step result must remain the stored lambda body");
    };
    let ExprNode::App(function, _) = fixture.kernel.expr_node(*body) else {
        panic!("the helper application must remain syntactically opaque");
    };
    assert!(matches!(
        fixture.kernel.expr_node(*function),
        ExprNode::Const(name, levels) if *name == fixture.helper && levels.is_empty()
    ));
}

#[test]
fn application_spine_is_preserved_but_not_beta_reduced() {
    let mut fixture = fixture();
    let zero = fixture.kernel.const_(fixture.logic.nat_zero, vec![]);
    let trace = build_source_delta_step(&mut fixture.kernel, fixture.source, &[], &[zero])
        .expect("applied source delta checks");
    assert_eq!(trace.arguments, vec![zero]);
    assert!(matches!(
        fixture.kernel.expr_node(trace.after),
        ExprNode::App(function, argument)
            if *function == fixture.source_value && *argument == zero
    ));
}

#[test]
fn wrong_head_and_wrong_body_fail_closed() {
    let mut fixture = fixture();
    let source_before = fixture.kernel.const_(fixture.source, vec![]);
    let helper_before = fixture.kernel.const_(fixture.helper, vec![]);
    let wrong_after = fixture.kernel.const_(fixture.logic.nat_zero, vec![]);
    assert_eq!(
        verify_source_delta_step(
            &mut fixture.kernel,
            fixture.source,
            helper_before,
            fixture.source_value,
        ),
        Err(SourceDeltaStepError::SourceHeadMismatch)
    );
    assert_eq!(
        verify_source_delta_step(
            &mut fixture.kernel,
            fixture.source,
            source_before,
            wrong_after,
        ),
        Err(SourceDeltaStepError::AfterMismatch)
    );
}

#[test]
fn theorem_and_wrong_universe_arity_are_rejected() {
    let mut fixture = fixture();
    assert_eq!(
        build_source_delta_step(&mut fixture.kernel, fixture.logic.eq_refl, &[], &[]),
        Err(SourceDeltaStepError::SourceNotDefinition)
    );

    let universe_name = name(&mut fixture.kernel, &["u"]);
    let universe = fixture.kernel.level_param(universe_name);
    let sort = fixture.kernel.sort(universe);
    let anonymous = fixture.kernel.anon();
    let identity_type = fixture
        .kernel
        .pi(anonymous, sort, sort, BinderInfo::Default);
    let identity_body = fixture.kernel.bvar(0);
    let identity_value = fixture
        .kernel
        .lam(anonymous, sort, identity_body, BinderInfo::Default);
    let polymorphic = name(&mut fixture.kernel, &["Trace", "poly"]);
    fixture
        .kernel
        .add_declaration(Declaration::Definition {
            name: polymorphic,
            uparams: vec![universe_name],
            ty: identity_type,
            value: identity_value,
            hint: ReducibilityHint::Regular(0),
        })
        .expect("polymorphic identity checks");
    assert_eq!(
        build_source_delta_step(&mut fixture.kernel, polymorphic, &[], &[]),
        Err(SourceDeltaStepError::UniverseArityMismatch {
            expected: 1,
            observed: 0,
        })
    );
}
