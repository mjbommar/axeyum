//! Kernel controls for ADR-0488's first discharged local function contract.

use axeyum_lean_import::{
    SemanticFunctionContractReceiptError, canonical_declaration_sha256,
    issue_semantic_function_contract_receipt, verify_semantic_function_contract_receipt,
};
use axeyum_lean_kernel::{
    BinderInfo, Declaration, ExprId, Kernel, LogicPrelude, NameId, ReducibilityHint,
    build_logic_prelude,
};

fn name(kernel: &mut Kernel, parts: &[&str]) -> NameId {
    let mut result = kernel.anon();
    for part in parts {
        result = kernel.name_str(result, *part);
    }
    result
}

fn eq(kernel: &mut Kernel, logic: &LogicPrelude, ty: ExprId, lhs: ExprId, rhs: ExprId) -> ExprId {
    let zero = kernel.level_zero();
    let one = kernel.level_succ(zero);
    let eq = kernel.const_(logic.eq, vec![one]);
    let eq = kernel.app(eq, ty);
    let eq = kernel.app(eq, lhs);
    kernel.app(eq, rhs)
}

fn refl(kernel: &mut Kernel, logic: &LogicPrelude, ty: ExprId, value: ExprId) -> ExprId {
    let zero = kernel.level_zero();
    let one = kernel.level_succ(zero);
    let refl = kernel.const_(logic.eq_refl, vec![one]);
    let refl = kernel.app(refl, ty);
    kernel.app(refl, value)
}

struct ContractFixture {
    kernel: Kernel,
    logic: LogicPrelude,
    source_id: NameId,
    source_succ: NameId,
    generalized_type: ExprId,
    generalized_proof: ExprId,
}

fn fixture() -> ContractFixture {
    let mut kernel = Kernel::new();
    let logic = build_logic_prelude(&mut kernel).expect("logic prelude builds");
    let nat = kernel.const_(logic.nat, vec![]);
    let anonymous = kernel.anon();
    let function_type = kernel.pi(anonymous, nat, nat, BinderInfo::Default);

    let source_id = name(&mut kernel, &["Source", "id"]);
    let id_body = kernel.bvar(0);
    let id_value = kernel.lam(anonymous, nat, id_body, BinderInfo::Default);
    kernel
        .add_declaration(Declaration::Definition {
            name: source_id,
            uparams: vec![],
            ty: function_type,
            value: id_value,
            hint: ReducibilityHint::Regular(0),
        })
        .expect("source identity definition checks");

    let source_succ = name(&mut kernel, &["Source", "succ"]);
    let succ = kernel.const_(logic.nat_succ, vec![]);
    let succ_argument = kernel.bvar(0);
    let succ_body = kernel.app(succ, succ_argument);
    let succ_value = kernel.lam(anonymous, nat, succ_body, BinderInfo::Default);
    kernel
        .add_declaration(Declaration::Definition {
            name: source_succ,
            uparams: vec![],
            ty: function_type,
            value: succ_value,
            hint: ReducibilityHint::Regular(0),
        })
        .expect("different same-typed source definition checks");

    // Under `f`, require the local behavior contract `forall x, f x = x`.
    let contract_x = kernel.bvar(0);
    let contract_f = kernel.bvar(1);
    let applied_contract_function = kernel.app(contract_f, contract_x);
    let contract_body = eq(
        &mut kernel,
        &logic,
        nat,
        applied_contract_function,
        contract_x,
    );
    let contract = kernel.pi(anonymous, nat, contract_body, BinderInfo::Default);

    // Under `f, h`, ask `forall n, f n = n`.
    let target_n = kernel.bvar(0);
    let target_f = kernel.bvar(2);
    let applied_target_function = kernel.app(target_f, target_n);
    let target_body = eq(&mut kernel, &logic, nat, applied_target_function, target_n);
    let target = kernel.pi(anonymous, nat, target_body, BinderInfo::Default);
    let with_contract = kernel.pi(anonymous, contract, target, BinderInfo::Default);
    let generalized_type = kernel.pi(anonymous, function_type, with_contract, BinderInfo::Default);

    // `fun f h n => h n`: proof search sees behavior only through the local
    // contract. No source definition or upstream theorem enters this term.
    let local_contract = kernel.bvar(1);
    let local_argument = kernel.bvar(0);
    let use_contract = kernel.app(local_contract, local_argument);
    let generalized_proof = kernel.lam(anonymous, nat, use_contract, BinderInfo::Default);
    let generalized_proof = kernel.lam(anonymous, contract, generalized_proof, BinderInfo::Default);
    let generalized_proof = kernel.lam(
        anonymous,
        function_type,
        generalized_proof,
        BinderInfo::Default,
    );

    ContractFixture {
        kernel,
        logic,
        source_id,
        source_succ,
        generalized_type,
        generalized_proof,
    }
}

fn source_contract(kernel: &mut Kernel, logic: &LogicPrelude, source: NameId) -> (ExprId, ExprId) {
    let anonymous = kernel.anon();
    let nat = kernel.const_(logic.nat, vec![]);
    let x = kernel.bvar(0);
    let source = kernel.const_(source, vec![]);
    let source_x = kernel.app(source, x);
    let body = eq(kernel, logic, nat, source_x, x);
    let ty = kernel.pi(anonymous, nat, body, BinderInfo::Default);
    let proof_body = refl(kernel, logic, nat, x);
    let proof = kernel.lam(anonymous, nat, proof_body, BinderInfo::Default);
    (ty, proof)
}

fn proof_kernel() -> (Kernel, NameId) {
    let mut kernel = Kernel::new();
    let logic = build_logic_prelude(&mut kernel).expect("proof logic prelude builds");
    let nat = kernel.const_(logic.nat, vec![]);
    let anonymous = kernel.anon();
    let function_type = kernel.pi(anonymous, nat, nat, BinderInfo::Default);
    let contract_x = kernel.bvar(0);
    let contract_f = kernel.bvar(1);
    let applied_contract_function = kernel.app(contract_f, contract_x);
    let contract_body = eq(
        &mut kernel,
        &logic,
        nat,
        applied_contract_function,
        contract_x,
    );
    let contract = kernel.pi(anonymous, nat, contract_body, BinderInfo::Default);
    let target_n = kernel.bvar(0);
    let target_f = kernel.bvar(2);
    let applied_target_function = kernel.app(target_f, target_n);
    let target_body = eq(&mut kernel, &logic, nat, applied_target_function, target_n);
    let target = kernel.pi(anonymous, nat, target_body, BinderInfo::Default);
    let with_contract = kernel.pi(anonymous, contract, target, BinderInfo::Default);
    let generic_type = kernel.pi(anonymous, function_type, with_contract, BinderInfo::Default);
    let local_contract = kernel.bvar(1);
    let local_argument = kernel.bvar(0);
    let proof = kernel.app(local_contract, local_argument);
    let proof = kernel.lam(anonymous, nat, proof, BinderInfo::Default);
    let proof = kernel.lam(anonymous, contract, proof, BinderInfo::Default);
    let proof = kernel.lam(anonymous, function_type, proof, BinderInfo::Default);
    let generic = name(&mut kernel, &["Generated", "use_id_contract"]);
    kernel
        .add_declaration(Declaration::Theorem {
            name: generic,
            uparams: vec![],
            ty: generic_type,
            value: proof,
        })
        .expect("generic proof checks in its isolated kernel");
    (kernel, generic)
}

#[test]
#[allow(clippy::too_many_lines)]
fn local_contract_and_source_witness_close_without_axioms() {
    let (mut independent, independent_generic) = proof_kernel();
    let mut fixture = fixture();
    let generic = name(&mut fixture.kernel, &["Generated", "use_id_contract"]);
    fixture
        .kernel
        .add_declaration(Declaration::Theorem {
            name: generic,
            uparams: vec![],
            ty: fixture.generalized_type,
            value: fixture.generalized_proof,
        })
        .expect("local-contract proof checks in the independent kernel");
    assert!(fixture.kernel.axiom_footprint(generic).is_empty());
    assert!(fixture.kernel.theorem_dependencies(generic).is_empty());

    let (witness_type, witness_proof) =
        source_contract(&mut fixture.kernel, &fixture.logic, fixture.source_id);
    let witness = name(&mut fixture.kernel, &["Generated", "source_id_contract"]);
    fixture
        .kernel
        .add_declaration(Declaration::Theorem {
            name: witness,
            uparams: vec![],
            ty: witness_type,
            value: witness_proof,
        })
        .expect("transparent source behavior discharges the contract");
    assert!(fixture.kernel.axiom_footprint(witness).is_empty());
    assert!(fixture.kernel.theorem_dependencies(witness).is_empty());

    let source = fixture.kernel.const_(fixture.source_id, vec![]);
    let generic_term = fixture.kernel.const_(generic, vec![]);
    let specialized = fixture.kernel.app(generic_term, source);
    let witness_term = fixture.kernel.const_(witness, vec![]);
    let specialized = fixture.kernel.app(specialized, witness_term);
    let concrete = name(&mut fixture.kernel, &["Generated", "source_id_result"]);
    let concrete_type = witness_type;
    fixture
        .kernel
        .add_declaration(Declaration::Theorem {
            name: concrete,
            uparams: vec![],
            ty: concrete_type,
            value: specialized,
        })
        .expect("checked contract specialization closes the concrete theorem");
    assert!(fixture.kernel.axiom_footprint(concrete).is_empty());
    let dependencies = fixture.kernel.theorem_dependencies(concrete);
    assert_eq!(dependencies.len(), 2);
    assert!(dependencies.contains(&generic));
    assert!(dependencies.contains(&witness));

    let receipt = issue_semantic_function_contract_receipt(
        &mut independent,
        independent_generic,
        &mut fixture.kernel,
        fixture.source_id,
        generic,
        witness,
        concrete,
        "synthetic-pointwise-function-contract-v1",
    )
    .expect("the two kernels issue one exact-source receipt");
    assert!(receipt.has_valid_digest());
    assert!(receipt.axiom_footprint.is_empty());
    assert_eq!(receipt.source_binder_position, 0);
    assert_eq!(receipt.contract_binder_position, 1);
    assert!(
        receipt
            .source_witness_dependencies
            .iter()
            .any(|dependency| dependency.name == "Source.id")
    );
    verify_semantic_function_contract_receipt(
        &receipt,
        &mut independent,
        independent_generic,
        &mut fixture.kernel,
        fixture.source_id,
        generic,
        witness,
        concrete,
    )
    .expect("the receipt reissues exactly");

    for mutate in [
        |receipt: &mut axeyum_lean_import::SemanticFunctionContractReceipt| {
            receipt.source_content_sha256 = "mutated".to_owned();
        },
        |receipt: &mut axeyum_lean_import::SemanticFunctionContractReceipt| {
            receipt.specialized_contract_sha256 = "mutated".to_owned();
        },
        |receipt: &mut axeyum_lean_import::SemanticFunctionContractReceipt| {
            receipt.contract_binder_position = 2;
        },
        |receipt: &mut axeyum_lean_import::SemanticFunctionContractReceipt| {
            receipt.source_witness_proof_sha256 = "mutated".to_owned();
        },
    ] {
        let mut mutated = receipt.clone();
        mutate(&mut mutated);
        assert!(matches!(
            verify_semantic_function_contract_receipt(
                &mutated,
                &mut independent,
                independent_generic,
                &mut fixture.kernel,
                fixture.source_id,
                generic,
                witness,
                concrete,
            ),
            Err(SemanticFunctionContractReceiptError::ReceiptMismatch)
        ));
    }

    assert!(matches!(
        issue_semantic_function_contract_receipt(
            &mut independent,
            independent_generic,
            &mut fixture.kernel,
            fixture.source_succ,
            generic,
            witness,
            concrete,
            "synthetic-pointwise-function-contract-v1",
        ),
        Err(SemanticFunctionContractReceiptError::WitnessTypeMismatch)
    ));
    assert!(matches!(
        issue_semantic_function_contract_receipt(
            &mut independent,
            independent_generic,
            &mut fixture.kernel,
            fixture.source_id,
            witness,
            witness,
            concrete,
            "synthetic-pointwise-function-contract-v1",
        ),
        Err(SemanticFunctionContractReceiptError::GenericMirrorMismatch)
    ));

    let direct = name(
        &mut fixture.kernel,
        &["Generated", "direct_source_id_result"],
    );
    fixture
        .kernel
        .add_declaration(Declaration::Theorem {
            name: direct,
            uparams: vec![],
            ty: concrete_type,
            value: witness_proof,
        })
        .expect("direct proof is a typed negative control");
    assert!(matches!(
        issue_semantic_function_contract_receipt(
            &mut independent,
            independent_generic,
            &mut fixture.kernel,
            fixture.source_id,
            generic,
            witness,
            direct,
            "synthetic-pointwise-function-contract-v1",
        ),
        Err(SemanticFunctionContractReceiptError::ConcreteProofMismatch)
    ));
}

#[test]
fn same_type_different_definition_has_a_different_identity_and_rejects_the_witness() {
    let mut fixture = fixture();
    assert_ne!(
        canonical_declaration_sha256(&fixture.kernel, fixture.source_id).unwrap(),
        canonical_declaration_sha256(&fixture.kernel, fixture.source_succ).unwrap()
    );
    let (wrong_type, reflexivity) =
        source_contract(&mut fixture.kernel, &fixture.logic, fixture.source_succ);
    let wrong = name(&mut fixture.kernel, &["Generated", "wrong_contract"]);
    assert!(
        fixture
            .kernel
            .add_declaration(Declaration::Theorem {
                name: wrong,
                uparams: vec![],
                ty: wrong_type,
                value: reflexivity,
            })
            .is_err(),
        "a same-typed but behaviorally different source must reject the witness"
    );
}

#[test]
fn circular_source_answer_is_visible_in_the_axiom_footprint() {
    let (mut independent, independent_generic) = proof_kernel();
    let mut fixture = fixture();
    let generic = name(&mut fixture.kernel, &["Generated", "use_id_contract"]);
    fixture
        .kernel
        .add_declaration(Declaration::Theorem {
            name: generic,
            uparams: vec![],
            ty: fixture.generalized_type,
            value: fixture.generalized_proof,
        })
        .expect("source kernel admits the exact generic mirror");
    let (contract_type, _) =
        source_contract(&mut fixture.kernel, &fixture.logic, fixture.source_id);
    let answer = name(&mut fixture.kernel, &["Upstream", "answer"]);
    fixture
        .kernel
        .add_declaration(Declaration::Axiom {
            name: answer,
            uparams: vec![],
            ty: contract_type,
        })
        .expect("control answer axiom has the contract type");
    let contaminated = name(&mut fixture.kernel, &["Generated", "contaminated_witness"]);
    let answer_term = fixture.kernel.const_(answer, vec![]);
    fixture
        .kernel
        .add_declaration(Declaration::Theorem {
            name: contaminated,
            uparams: vec![],
            ty: contract_type,
            value: answer_term,
        })
        .expect("type checking alone cannot establish answer isolation");
    assert_eq!(fixture.kernel.axiom_footprint(contaminated), vec![answer]);

    let generic_term = fixture.kernel.const_(generic, vec![]);
    let source_term = fixture.kernel.const_(fixture.source_id, vec![]);
    let applied = fixture.kernel.app(generic_term, source_term);
    let contaminated_term = fixture.kernel.const_(contaminated, vec![]);
    let applied = fixture.kernel.app(applied, contaminated_term);
    let concrete = name(&mut fixture.kernel, &["Generated", "contaminated_result"]);
    fixture
        .kernel
        .add_declaration(Declaration::Theorem {
            name: concrete,
            uparams: vec![],
            ty: contract_type,
            value: applied,
        })
        .expect("the source kernel exposes why assurance is a separate gate");
    assert!(matches!(
        issue_semantic_function_contract_receipt(
            &mut independent,
            independent_generic,
            &mut fixture.kernel,
            fixture.source_id,
            generic,
            contaminated,
            concrete,
            "synthetic-pointwise-function-contract-v1",
        ),
        Err(SemanticFunctionContractReceiptError::WitnessNotIndependent)
    ));
}
