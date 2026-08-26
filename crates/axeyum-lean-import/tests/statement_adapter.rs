//! Proof-isolated statement adapter controls for the Autogenesis nursery.

use std::io::Cursor;

use axeyum_lean_import::{
    ImportLimits, StatementImportError, import_candidate_statement_ndjson, import_statement_ndjson,
};
use axeyum_lean_kernel::{BinderInfo, Declaration, Kernel, Lean4ExportMetadata, ReducibilityHint};

const TARGET: &str = "Axeyum.Autogenesis.Statement.target";

fn target_name(kernel: &mut Kernel) -> axeyum_lean_kernel::NameId {
    let root = kernel.anon();
    let axeyum = kernel.name_str(root, "Axeyum");
    let autogenesis = kernel.name_str(axeyum, "Autogenesis");
    let statement = kernel.name_str(autogenesis, "Statement");
    kernel.name_str(statement, "target")
}

fn proposition(kernel: &mut Kernel) -> (axeyum_lean_kernel::ExprId, axeyum_lean_kernel::ExprId) {
    let zero = kernel.level_zero();
    let prop = kernel.sort(zero);
    let p = kernel.bvar(0);
    let root = kernel.anon();
    let binder = kernel.name_str(root, "p");
    let goal = kernel.pi(binder, prop, p, BinderInfo::Default);
    (prop, goal)
}

fn render(kernel: &Kernel) -> String {
    kernel
        .render_lean4export_ndjson(&Lean4ExportMetadata::axeyum("4.30.0"))
        .expect("test stream must render")
}

fn definition_stream() -> String {
    let mut kernel = Kernel::new();
    let name = target_name(&mut kernel);
    let (prop, goal) = proposition(&mut kernel);
    kernel
        .add_declaration(Declaration::Definition {
            name,
            uparams: vec![],
            ty: prop,
            value: goal,
            hint: ReducibilityHint::Regular(0),
        })
        .expect("goal definition must check");
    render(&kernel)
}

fn candidate_stream() -> (String, String) {
    let mut kernel = Kernel::new();
    let target = target_name(&mut kernel);
    let zero = kernel.level_zero();
    let prop = kernel.sort(zero);
    let root = kernel.anon();
    let p_name = kernel.name_str(root, "p");
    let h_name = kernel.name_str(root, "h");
    let p = kernel.bvar(0);
    let result = kernel.bvar(1);
    let implication = kernel.pi(h_name, p, result, BinderInfo::Default);
    let goal = kernel.pi(p_name, prop, implication, BinderInfo::Default);
    kernel
        .add_declaration(Declaration::Definition {
            name: target,
            uparams: vec![],
            ty: prop,
            value: goal,
            hint: ReducibilityHint::Regular(0),
        })
        .expect("goal definition must check");
    let candidate = kernel.name_str(root, "CandidateIdentity");
    let h = kernel.bvar(0);
    let p = kernel.bvar(0);
    let identity = kernel.lam(h_name, p, h, BinderInfo::Default);
    let proof = kernel.lam(p_name, prop, identity, BinderInfo::Default);
    kernel
        .add_declaration(Declaration::Theorem {
            name: candidate,
            uparams: vec![],
            ty: goal,
            value: proof,
        })
        .expect("candidate theorem must check");
    (render(&kernel), "CandidateIdentity".to_owned())
}

#[test]
fn transparent_prop_definition_publishes_a_goal_without_an_assumption() {
    let completed = import_statement_ndjson(
        Cursor::new(definition_stream()),
        ImportLimits::default(),
        TARGET,
    )
    .expect("proof-free statement must import");
    assert_eq!(completed.report().axioms, Vec::<String>::new());
    assert_eq!(completed.report().declaration_identities.len(), 1);
    assert_eq!(
        completed.kernel().render_lean(completed.goal()),
        "((p : Prop) -> p)"
    );
    assert_eq!(
        completed
            .kernel()
            .display_name(completed.target_name())
            .to_string(),
        TARGET
    );
}

#[test]
fn explicit_axiom_free_theorem_candidate_is_checked_and_published() {
    let (stream, candidate) = candidate_stream();
    let completed = import_candidate_statement_ndjson(
        Cursor::new(stream),
        ImportLimits::default(),
        TARGET,
        std::slice::from_ref(&candidate),
    )
    .expect("the exact checked candidate must import");
    assert!(
        completed
            .kernel()
            .axiom_footprint(
                completed
                    .kernel()
                    .environment()
                    .iter()
                    .find(
                        |(name, _)| completed.kernel().display_name(**name).to_string()
                            == candidate
                    )
                    .map(|(name, _)| *name)
                    .expect("candidate must be published")
            )
            .is_empty()
    );
}

#[test]
fn unlisted_theorem_remains_forbidden_in_candidate_capsule() {
    let (stream, _candidate) = candidate_stream();
    let error = import_candidate_statement_ndjson(
        Cursor::new(stream),
        ImportLimits::default(),
        TARGET,
        &[],
    )
    .expect_err("an unlisted theorem must poison the capsule");
    assert!(matches!(
        error,
        StatementImportError::TrustedDeclaration { .. }
    ));
}

#[test]
fn candidate_identity_list_is_exact_and_cannot_name_the_target() {
    let (stream, candidate) = candidate_stream();
    let duplicate = import_candidate_statement_ndjson(
        Cursor::new(stream.clone()),
        ImportLimits::default(),
        TARGET,
        &[candidate.clone(), candidate],
    )
    .expect_err("duplicate candidate names must be rejected");
    assert!(matches!(
        duplicate,
        StatementImportError::DuplicateCandidate
    ));

    let target = import_candidate_statement_ndjson(
        Cursor::new(stream),
        ImportLimits::default(),
        TARGET,
        &[TARGET.to_owned()],
    )
    .expect_err("the target cannot be its own candidate");
    assert!(matches!(
        target,
        StatementImportError::CandidateIsTarget { .. }
    ));
}

#[test]
fn proof_bearing_target_is_rejected() {
    let mut kernel = Kernel::new();
    let name = target_name(&mut kernel);
    let (prop, goal) = proposition(&mut kernel);
    kernel
        .add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty: prop,
            value: goal,
        })
        .expect("control theorem must check");
    let error = import_statement_ndjson(
        Cursor::new(render(&kernel)),
        ImportLimits::default(),
        TARGET,
    )
    .expect_err("theorem target must not enter the statement adapter");
    assert!(matches!(
        error,
        StatementImportError::TrustedDeclaration { .. }
    ));
}

#[test]
fn unrelated_axiom_is_rejected() {
    let mut kernel = Kernel::new();
    let target = target_name(&mut kernel);
    let (prop, goal) = proposition(&mut kernel);
    kernel
        .add_declaration(Declaration::Definition {
            name: target,
            uparams: vec![],
            ty: prop,
            value: goal,
            hint: ReducibilityHint::Regular(0),
        })
        .expect("goal definition must check");
    let root = kernel.anon();
    let assumption = kernel.name_str(root, "SmuggledAssumption");
    kernel
        .add_declaration(Declaration::Axiom {
            name: assumption,
            uparams: vec![],
            ty: prop,
        })
        .expect("control axiom must check");
    let error = import_statement_ndjson(
        Cursor::new(render(&kernel)),
        ImportLimits::default(),
        TARGET,
    )
    .expect_err("an unrelated assumption must poison the whole stream");
    assert!(matches!(
        error,
        StatementImportError::TrustedDeclaration { .. }
    ));
}

#[test]
fn type_valued_definition_is_not_a_goal() {
    let mut kernel = Kernel::new();
    let name = target_name(&mut kernel);
    let zero = kernel.level_zero();
    let one = kernel.level_succ(zero);
    let two = kernel.level_succ(one);
    let value = kernel.sort(one);
    let ty = kernel.sort(two);
    kernel
        .add_declaration(Declaration::Definition {
            name,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(0),
        })
        .expect("type-valued control definition must check");
    let error = import_statement_ndjson(
        Cursor::new(render(&kernel)),
        ImportLimits::default(),
        TARGET,
    )
    .expect_err("a Type-valued definition must not become a proof goal");
    assert!(matches!(error, StatementImportError::GoalNotProp { .. }));
}

#[test]
fn wrong_or_missing_target_name_is_rejected() {
    let error = import_statement_ndjson(
        Cursor::new(definition_stream()),
        ImportLimits::default(),
        "Axeyum.Autogenesis.Statement.other",
    )
    .expect_err("target identity must be exact");
    assert!(matches!(
        error,
        StatementImportError::TargetCardinality { observed: 0, .. }
    ));
}
