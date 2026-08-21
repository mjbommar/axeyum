//! Adversarial controls for source-bound checked theorem receipts.

use axeyum_lean_import::{
    CheckedDependencyTheoremAuthority, CheckedDependencyTheoremReceiptError,
    CheckedSemanticTheoremReceiptError, CheckedTheoremAuthority, CheckedTheoremDependency,
    canonical_declaration_sha256, canonical_expression_sha256,
    issue_checked_dependency_theorem_receipt, issue_checked_semantic_theorem_receipt,
    verify_checked_dependency_theorem_receipt, verify_checked_semantic_theorem_receipt,
};
use axeyum_lean_kernel::{BinderInfo, Declaration, Kernel, NameId, build_logic_prelude};

fn name(kernel: &mut Kernel, parts: &[&str]) -> NameId {
    let mut result = kernel.anon();
    for part in parts {
        result = kernel.name_str(result, *part);
    }
    result
}

fn reflexive_fixture() -> (Kernel, NameId, CheckedTheoremAuthority) {
    let mut kernel = Kernel::new();
    let logic = build_logic_prelude(&mut kernel).expect("logic prelude builds");
    let nat = kernel.const_(logic.nat, vec![]);
    let zero = kernel.level_zero();
    let one = kernel.level_succ(zero);
    let eq = kernel.const_(logic.eq, vec![one]);
    let eq = kernel.app(eq, nat);
    let bound = kernel.bvar(0);
    let eq = kernel.app(eq, bound);
    let eq = kernel.app(eq, bound);
    let anonymous = kernel.anon();
    let goal = kernel.pi(anonymous, nat, eq, BinderInfo::Default);
    let refl = kernel.const_(logic.eq_refl, vec![one]);
    let refl = kernel.app(refl, nat);
    let refl = kernel.app(refl, bound);
    let proof = kernel.lam(anonymous, nat, refl, BinderInfo::Default);
    let theorem = name(&mut kernel, &["Checked", "refl"]);
    kernel
        .add_declaration(Declaration::Theorem {
            name: theorem,
            uparams: vec![],
            ty: goal,
            value: proof,
        })
        .expect("synthetic theorem checks");
    let authority = CheckedTheoremAuthority {
        policy_version: "synthetic-checked-theorem-v1".to_owned(),
        source_artifact_sha256: "1".repeat(64),
        target_definition: "Synthetic.goal".to_owned(),
        fact_id: "F:synthetic-checked-theorem".to_owned(),
        goal_sha256: canonical_expression_sha256(&kernel, goal).expect("goal identity"),
        candidate_observation_sha256: "2".repeat(64),
        expected_proof_sha256: canonical_expression_sha256(&kernel, proof).expect("proof identity"),
        expected_theorem_content_sha256: canonical_declaration_sha256(&kernel, theorem)
            .expect("theorem identity"),
        operation: "synthetic-reflexivity-v1".to_owned(),
        max_plan_templates: 1,
        max_kernel_submissions: 1,
        max_executor_invocations: 1,
        max_retries: 0,
    };
    (kernel, theorem, authority)
}

#[test]
fn exact_candidate_issues_and_replays_one_receipt() {
    let (mut kernel, theorem, authority) = reflexive_fixture();
    let receipt = issue_checked_semantic_theorem_receipt(&mut kernel, theorem, &authority)
        .expect("receipt issues");
    assert!(receipt.has_valid_digest());
    assert!(receipt.axiom_footprint.is_empty());
    assert!(receipt.direct_theorem_dependencies.is_empty());
    assert!(receipt.to_pretty_json().unwrap().ends_with('\n'));
    verify_checked_semantic_theorem_receipt(&receipt, &mut kernel, theorem, &authority)
        .expect("receipt replays");
}

#[test]
fn authority_and_receipt_mutations_fail_closed() {
    let (mut kernel, theorem, authority) = reflexive_fixture();
    let receipt = issue_checked_semantic_theorem_receipt(&mut kernel, theorem, &authority)
        .expect("receipt issues");
    let mut wrong_authority = authority.clone();
    wrong_authority.expected_proof_sha256 = "0".repeat(64);
    assert_eq!(
        issue_checked_semantic_theorem_receipt(&mut kernel, theorem, &wrong_authority),
        Err(CheckedSemanticTheoremReceiptError::CandidateMismatch)
    );
    let mut mutated = receipt.clone();
    mutated.receipt_sha256 = "0".repeat(64);
    assert_eq!(
        verify_checked_semantic_theorem_receipt(&mutated, &mut kernel, theorem, &authority),
        Err(CheckedSemanticTheoremReceiptError::ReceiptMismatch)
    );
}

#[test]
fn axioms_and_direct_theorem_dependencies_are_rejected() {
    let mut kernel = Kernel::new();
    let logic = build_logic_prelude(&mut kernel).expect("logic prelude builds");
    let true_type = kernel.const_(logic.true_, vec![]);
    let assumed = name(&mut kernel, &["Checked", "assumed"]);
    kernel
        .add_declaration(Declaration::Axiom {
            name: assumed,
            uparams: vec![],
            ty: true_type,
        })
        .expect("axiom checks");
    let axiom_theorem = name(&mut kernel, &["Checked", "fromAxiom"]);
    let assumed_term = kernel.const_(assumed, vec![]);
    kernel
        .add_declaration(Declaration::Theorem {
            name: axiom_theorem,
            uparams: vec![],
            ty: true_type,
            value: assumed_term,
        })
        .expect("axiom-backed theorem checks");
    let authority_for = |kernel: &Kernel, theorem: NameId, proof: _| CheckedTheoremAuthority {
        policy_version: "synthetic-checked-theorem-v1".to_owned(),
        source_artifact_sha256: "1".repeat(64),
        target_definition: "Synthetic.goal".to_owned(),
        fact_id: "F:synthetic-checked-theorem".to_owned(),
        goal_sha256: canonical_expression_sha256(kernel, true_type).unwrap(),
        candidate_observation_sha256: "2".repeat(64),
        expected_proof_sha256: canonical_expression_sha256(kernel, proof).unwrap(),
        expected_theorem_content_sha256: canonical_declaration_sha256(kernel, theorem).unwrap(),
        operation: "synthetic-reflexivity-v1".to_owned(),
        max_plan_templates: 1,
        max_kernel_submissions: 1,
        max_executor_invocations: 1,
        max_retries: 0,
    };
    let axiom_authority = authority_for(&kernel, axiom_theorem, assumed_term);
    assert!(matches!(
        issue_checked_semantic_theorem_receipt(&mut kernel, axiom_theorem, &axiom_authority),
        Err(CheckedSemanticTheoremReceiptError::AxiomFootprint { .. })
    ));

    let base = name(&mut kernel, &["Checked", "base"]);
    let intro = kernel.const_(logic.true_intro, vec![]);
    kernel
        .add_declaration(Declaration::Theorem {
            name: base,
            uparams: vec![],
            ty: true_type,
            value: intro,
        })
        .expect("base theorem checks");
    let dependent = name(&mut kernel, &["Checked", "dependent"]);
    let base_term = kernel.const_(base, vec![]);
    kernel
        .add_declaration(Declaration::Theorem {
            name: dependent,
            uparams: vec![],
            ty: true_type,
            value: base_term,
        })
        .expect("dependent theorem checks");
    let dependent_authority = authority_for(&kernel, dependent, base_term);
    assert!(matches!(
        issue_checked_semantic_theorem_receipt(&mut kernel, dependent, &dependent_authority),
        Err(CheckedSemanticTheoremReceiptError::TheoremDependencies { .. })
    ));
}

#[test]
fn exact_preregistered_dependency_issues_and_replays() {
    let (mut kernel, premise, mut theorem_authority) = reflexive_fixture();
    let premise_type = kernel
        .environment()
        .get(premise)
        .expect("premise exists")
        .ty();
    let proof = kernel.const_(premise, vec![]);
    let theorem = name(&mut kernel, &["Checked", "dependent"]);
    kernel
        .add_declaration(Declaration::Theorem {
            name: theorem,
            uparams: vec![],
            ty: premise_type,
            value: proof,
        })
        .expect("dependent theorem checks");
    theorem_authority.goal_sha256 =
        canonical_expression_sha256(&kernel, premise_type).expect("goal identity");
    theorem_authority.expected_proof_sha256 =
        canonical_expression_sha256(&kernel, proof).expect("proof identity");
    theorem_authority.expected_theorem_content_sha256 =
        canonical_declaration_sha256(&kernel, theorem).expect("theorem identity");
    theorem_authority.operation = "synthetic-dependent-v1".to_owned();
    let dependency = CheckedTheoremDependency {
        name: "Checked.refl".to_owned(),
        content_sha256: canonical_declaration_sha256(&kernel, premise)
            .expect("dependency identity"),
    };
    let authority = CheckedDependencyTheoremAuthority {
        theorem: theorem_authority,
        expected_direct_theorem_dependencies: vec![dependency],
    };
    let receipt = issue_checked_dependency_theorem_receipt(&mut kernel, theorem, &authority)
        .expect("dependency-bound receipt issues");
    assert!(receipt.has_valid_digest());
    assert!(receipt.axiom_footprint.is_empty());
    assert_eq!(
        receipt.direct_theorem_dependencies,
        authority.expected_direct_theorem_dependencies
    );
    verify_checked_dependency_theorem_receipt(&receipt, &mut kernel, theorem, &authority)
        .expect("dependency-bound receipt replays");
}

#[test]
fn dependency_authority_and_receipt_mutations_fail_closed() {
    let (mut kernel, premise, mut theorem_authority) = reflexive_fixture();
    let premise_type = kernel
        .environment()
        .get(premise)
        .expect("premise exists")
        .ty();
    let proof = kernel.const_(premise, vec![]);
    let theorem = name(&mut kernel, &["Checked", "dependent"]);
    kernel
        .add_declaration(Declaration::Theorem {
            name: theorem,
            uparams: vec![],
            ty: premise_type,
            value: proof,
        })
        .expect("dependent theorem checks");
    theorem_authority.goal_sha256 =
        canonical_expression_sha256(&kernel, premise_type).expect("goal identity");
    theorem_authority.expected_proof_sha256 =
        canonical_expression_sha256(&kernel, proof).expect("proof identity");
    theorem_authority.expected_theorem_content_sha256 =
        canonical_declaration_sha256(&kernel, theorem).expect("theorem identity");
    theorem_authority.operation = "synthetic-dependent-v1".to_owned();
    let authority = CheckedDependencyTheoremAuthority {
        theorem: theorem_authority,
        expected_direct_theorem_dependencies: vec![CheckedTheoremDependency {
            name: "Checked.refl".to_owned(),
            content_sha256: canonical_declaration_sha256(&kernel, premise)
                .expect("dependency identity"),
        }],
    };
    let receipt = issue_checked_dependency_theorem_receipt(&mut kernel, theorem, &authority)
        .expect("dependency-bound receipt issues");

    let mut wrong_dependency = authority.clone();
    wrong_dependency.expected_direct_theorem_dependencies[0].content_sha256 = "0".repeat(64);
    assert!(matches!(
        issue_checked_dependency_theorem_receipt(&mut kernel, theorem, &wrong_dependency),
        Err(CheckedDependencyTheoremReceiptError::DependencyMismatch { .. })
    ));

    let mut empty_dependencies = authority.clone();
    empty_dependencies
        .expected_direct_theorem_dependencies
        .clear();
    assert_eq!(
        issue_checked_dependency_theorem_receipt(&mut kernel, theorem, &empty_dependencies),
        Err(CheckedDependencyTheoremReceiptError::InvalidAuthority)
    );

    let mut mutated = receipt.clone();
    mutated.direct_theorem_dependencies[0].content_sha256 = "0".repeat(64);
    assert_eq!(
        verify_checked_dependency_theorem_receipt(&mutated, &mut kernel, theorem, &authority),
        Err(CheckedDependencyTheoremReceiptError::ReceiptMismatch)
    );
}
