use axeyum_lean_kernel::{Declaration, Kernel, ReducibilityHint, build_logic_prelude};

use super::*;

fn name(kernel: &mut Kernel, value: &str) -> NameId {
    let anon = kernel.anon();
    kernel.name_str(anon, value)
}

fn add_true_theorem(kernel: &mut Kernel, name: &str) -> NameId {
    let logic = build_logic_prelude(kernel).expect("logic prelude");
    let theorem = self::name(kernel, name);
    let ty = kernel.const_(logic.true_, vec![]);
    let value = kernel.const_(logic.true_intro, vec![]);
    kernel
        .add_declaration(Declaration::Theorem {
            name: theorem,
            uparams: vec![],
            ty,
            value,
        })
        .expect("true theorem");
    theorem
}

#[test]
fn completed_composition_is_axiom_free_deterministic_and_reverifiable() {
    let mut source = Kernel::new();
    add_true_theorem(&mut source, "Composition.root");
    let mut target = Kernel::new();
    build_logic_prelude(&mut target).expect("target logic");
    let target_before = environment_sha256(&target).unwrap();
    let target_len = target.environment().len();

    let first = compose_checked_theorem_slice(&source, &target, &["Composition.root"]).unwrap();
    let second = compose_checked_theorem_slice(&source, &target, &["Composition.root"]).unwrap();
    assert_eq!(first.receipt(), second.receipt());
    assert!(first.receipt().has_valid_digest());
    assert!(first.receipt().to_pretty_json().unwrap().ends_with('\n'));
    assert_eq!(target.environment().len(), target_len);
    assert_eq!(environment_sha256(&target).unwrap(), target_before);
    assert_eq!(first.receipt().added_theorems.len(), 1);
    assert_eq!(first.receipt().added_theorems[0].name, "Composition.root");
    assert!(first.receipt().added_theorems[0].axiom_footprint.is_empty());
    assert!(declaration_names(first.kernel()).contains_key("Composition.root"));
    verify_checked_theorem_composition(&source, &target, first.kernel(), first.receipt()).unwrap();

    assert!(matches!(
        compose_checked_theorem_slice(&source, first.kernel(), &["Composition.root"]),
        Err(CheckedTheoremCompositionError::NoAdditions)
    ));
}

#[test]
fn roots_and_missing_non_theorems_fail_closed() {
    let mut source = Kernel::new();
    let logic = build_logic_prelude(&mut source).expect("source logic");
    let target = {
        let mut kernel = Kernel::new();
        build_logic_prelude(&mut kernel).expect("target logic");
        kernel
    };
    assert!(matches!(
        compose_checked_theorem_slice(&source, &target, &[]),
        Err(CheckedTheoremCompositionError::EmptyRoots)
    ));
    assert!(matches!(
        compose_checked_theorem_slice(&source, &target, &["missing"]),
        Err(CheckedTheoremCompositionError::MissingRoot(name)) if name == "missing"
    ));
    assert!(matches!(
        compose_checked_theorem_slice(&source, &target, &["True"]),
        Err(CheckedTheoremCompositionError::RootIsNotTheorem(name)) if name == "True"
    ));

    let anon = source.anon();
    let definition = source.name_str(anon, "Composition.payload");
    let prop = source.sort_zero();
    let true_type = source.const_(logic.true_, vec![]);
    source
        .add_declaration(Declaration::Definition {
            name: definition,
            uparams: vec![],
            ty: prop,
            value: true_type,
            hint: ReducibilityHint::Regular(1),
        })
        .unwrap();
    let root = source.name_str(anon, "Composition.definitionRoot");
    let root_type = source.const_(definition, vec![]);
    let proof = source.const_(logic.true_intro, vec![]);
    source
        .add_declaration(Declaration::Theorem {
            name: root,
            uparams: vec![],
            ty: root_type,
            value: proof,
        })
        .unwrap();
    assert!(matches!(
        compose_checked_theorem_slice(&source, &target, &["Composition.definitionRoot"]),
        Err(CheckedTheoremCompositionError::UnsupportedMissingDeclaration { name, kind })
            if name == "Composition.payload" && kind == "definition"
    ));
}

#[test]
fn a_structural_reuse_mismatch_leaves_the_target_unchanged() {
    let mut source = Kernel::new();
    build_logic_prelude(&mut source).unwrap();
    let mut target = Kernel::new();
    build_logic_prelude(&mut target).unwrap();
    let source_name = name(&mut source, "Composition.P");
    let target_name = name(&mut target, "Composition.P");
    let source_prop = source.sort_zero();
    source
        .add_declaration(Declaration::Axiom {
            name: source_name,
            uparams: vec![],
            ty: source_prop,
        })
        .unwrap();
    let target_type = {
        let zero = target.level_zero();
        let one = target.level_succ(zero);
        target.sort(one)
    };
    target
        .add_declaration(Declaration::Axiom {
            name: target_name,
            uparams: vec![],
            ty: target_type,
        })
        .unwrap();
    let witness_name = name(&mut source, "Composition.p");
    let proposition = source.const_(source_name, vec![]);
    source
        .add_declaration(Declaration::Axiom {
            name: witness_name,
            uparams: vec![],
            ty: proposition,
        })
        .unwrap();
    let root_name = name(&mut source, "Composition.mismatchRoot");
    let witness = source.const_(witness_name, vec![]);
    source
        .add_declaration(Declaration::Theorem {
            name: root_name,
            uparams: vec![],
            ty: proposition,
            value: witness,
        })
        .unwrap();
    let before = environment_sha256(&target).unwrap();
    assert!(matches!(
        compose_checked_theorem_slice(&source, &target, &["Composition.mismatchRoot"]),
        Err(CheckedTheoremCompositionError::TypeShapeMismatch { name, .. })
            if name == "Composition.P"
    ));
    assert_eq!(environment_sha256(&target).unwrap(), before);
}

#[test]
fn admission_failure_after_staging_does_not_publish_the_prefix() {
    let mut source = Kernel::new();
    let source_logic = build_logic_prelude(&mut source).unwrap();
    let mut target = Kernel::new();
    let target_logic = build_logic_prelude(&mut target).unwrap();
    let source_definition = name(&mut source, "Composition.switch");
    let target_definition = name(&mut target, "Composition.switch");
    let source_prop = source.sort_zero();
    let target_prop = target.sort_zero();
    let source_true = source.const_(source_logic.true_, vec![]);
    let target_false = target.const_(target_logic.false_, vec![]);
    source
        .add_declaration(Declaration::Definition {
            name: source_definition,
            uparams: vec![],
            ty: source_prop,
            value: source_true,
            hint: ReducibilityHint::Regular(1),
        })
        .unwrap();
    target
        .add_declaration(Declaration::Definition {
            name: target_definition,
            uparams: vec![],
            ty: target_prop,
            value: target_false,
            hint: ReducibilityHint::Regular(1),
        })
        .unwrap();
    let helper = add_true_theorem(&mut source, "Composition.helper");
    let root = name(&mut source, "Composition.lateFailure");
    let root_type = source.const_(source_definition, vec![]);
    let helper_proof = source.const_(helper, vec![]);
    source
        .add_declaration(Declaration::Theorem {
            name: root,
            uparams: vec![],
            ty: root_type,
            value: helper_proof,
        })
        .unwrap();
    let before = environment_sha256(&target).unwrap();
    assert!(matches!(
        compose_checked_theorem_slice(&source, &target, &["Composition.lateFailure"]),
        Err(CheckedTheoremCompositionError::AdmissionRejected { name, .. })
            if name == "Composition.lateFailure"
    ));
    assert_eq!(environment_sha256(&target).unwrap(), before);
    assert!(!declaration_names(&target).contains_key("Composition.helper"));
}

#[test]
fn free_variables_and_receipt_mutations_are_rejected() {
    let mut source = Kernel::new();
    let free = source.fvar(7);
    let mut target = Kernel::new();
    assert_eq!(
        ExpressionTranslator::new(&source, &mut target).expr(free),
        Err(CheckedTheoremCompositionError::FreeVariable)
    );

    let mut source = Kernel::new();
    add_true_theorem(&mut source, "Composition.receiptRoot");
    let mut target = Kernel::new();
    build_logic_prelude(&mut target).unwrap();
    let completed =
        compose_checked_theorem_slice(&source, &target, &["Composition.receiptRoot"]).unwrap();
    let mut changed = completed.receipt().clone();
    changed.target_environment_sha256_after = "00".repeat(32);
    assert_eq!(
        verify_checked_theorem_composition(&source, &target, completed.kernel(), &changed),
        Err(CheckedTheoremCompositionError::ReceiptMismatch)
    );
}
