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

// ---------------------------------------------------------------------------
// The native quotient package (ADR-1667 / ADR-1662)
//
// Measured 2026-09-05: 73 of 756 pinned Mathlib statement mirrors were refused
// with `Quot` as the first blocker. The four quotient primitives are a type
// former and its eliminators, and `Kernel::add_quotient_package` derives all
// four types itself before admitting any of them, so nothing about the stream
// is trusted. `Quot.sound` — the one quotient fact that states a proposition —
// is absent from this kernel entirely and has no `quot.kind` spelling.
// ---------------------------------------------------------------------------

const QUOTIENT_FIXTURE: &str =
    include_str!("../../../docs/plan/fixtures/lean4export-v4.30-quotient.ndjson");

/// A kernel carrying the real, kernel-validated quotient package (imported
/// from the pinned Lean 4.30 fixture) plus a transparent `Prop` target.
fn quotient_statement_kernel() -> Kernel {
    let completed = axeyum_lean_import::import_ndjson(
        Cursor::new(QUOTIENT_FIXTURE.as_bytes()),
        ImportLimits::default(),
    )
    .expect("quotient fixture must import");
    let (mut kernel, _report) = completed.into_parts();
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
    kernel
}

/// POSITIVE control for the admission feature: a statement stream whose
/// closure carries the complete, kernel-validated quotient package now
/// crosses. Before ADR-1667 this returned
/// `StatementImportError::TrustedDeclaration { name: "Quot", .. }`.
#[test]
fn the_native_quotient_package_does_not_block_a_statement() {
    let kernel = quotient_statement_kernel();
    let completed = import_statement_ndjson(
        Cursor::new(render(&kernel)),
        ImportLimits::default(),
        TARGET,
    )
    .expect("a statement closure carrying the native quotient package must cross");
    let report = completed.report();
    let mut admitted = report.native_quotient_package.clone();
    admitted.sort();
    assert_eq!(
        admitted,
        vec![
            "Quot".to_owned(),
            "Quot.ind".to_owned(),
            "Quot.lift".to_owned(),
            "Quot.mk".to_owned()
        ],
        "exactly the four package members must be recorded as natively admitted"
    );
    assert!(
        !report
            .native_quotient_package
            .iter()
            .any(|n| n == "Quot.sound"),
        "Quot.sound must never appear: this kernel does not have it"
    );

    // The exemption is about ADMITTING a statement, never about what a later
    // proof may claim: `Kernel::axiom_footprint` must still classify every
    // package member as trusted base, so a theorem that reaches one is still
    // visibly not axiom-free (ADR-1595 prices the quotient package on exactly
    // this accounting). Measured here rather than asserted in a comment.
    let kernel = completed.kernel();
    for member in ["Quot", "Quot.mk", "Quot.lift", "Quot.ind"] {
        let name = kernel
            .environment()
            .iter()
            .find(|(name, _)| kernel.display_name(**name).to_string() == member)
            .map(|(name, _)| *name)
            .unwrap_or_else(|| panic!("{member} must be in the admitted environment"));
        let footprint: Vec<String> = kernel
            .axiom_footprint(name)
            .into_iter()
            .map(|n| kernel.display_name(n).to_string())
            .collect();
        assert!(
            footprint.iter().any(|n| n == member),
            "{member} must still count toward its own axiom footprint; got {footprint:?}"
        );
    }
}

/// NEGATIVE control for the same feature: the quotient exemption must not
/// widen to anything else in the same stream. An ordinary smuggled `Theorem`
/// alongside the very same validated quotient package is still refused, so
/// the new `continue` cannot be the reason a proof-bearing declaration got in.
#[test]
fn the_quotient_exemption_does_not_admit_a_theorem_beside_it() {
    let mut kernel = quotient_statement_kernel();
    let root = kernel.anon();
    let smuggled = kernel.name_str(root, "SmuggledTheorem");
    // A genuinely provable proposition (`forall p : Prop, p -> p`), so this
    // control fails at the ISOLATION GATE and not at the kernel — a theorem
    // the kernel refuses would make the test pass for the wrong reason.
    let zero = kernel.level_zero();
    let prop = kernel.sort(zero);
    let p_name = kernel.name_str(root, "p");
    let h_name = kernel.name_str(root, "h");
    let p = kernel.bvar(0);
    let result = kernel.bvar(1);
    let implication = kernel.pi(h_name, p, result, BinderInfo::Default);
    let statement = kernel.pi(p_name, prop, implication, BinderInfo::Default);
    let h = kernel.bvar(0);
    let p = kernel.bvar(0);
    let identity = kernel.lam(h_name, p, h, BinderInfo::Default);
    let proof = kernel.lam(p_name, prop, identity, BinderInfo::Default);
    kernel
        .add_declaration(Declaration::Theorem {
            name: smuggled,
            uparams: vec![],
            ty: statement,
            value: proof,
        })
        .expect("control theorem must check");
    let error = import_statement_ndjson(
        Cursor::new(render(&kernel)),
        ImportLimits::default(),
        TARGET,
    )
    .expect_err("a theorem beside the quotient package must still poison the stream");
    match error {
        StatementImportError::TrustedDeclaration { name, .. } => {
            assert_eq!(name, "SmuggledTheorem");
        }
        other => panic!("expected TrustedDeclaration, got {other:?}"),
    }
}
